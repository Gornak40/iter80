const std = @import("std");

const Token = struct {
    type: Type,
    meta: ?[]const u8 = null,

    fn init(s: []const u8) Token {
        return if (std.mem.startsWith(u8, s, "__"))
            .{ .type = .__a, .meta = s[2..] }
        else if (std.mem.eql(u8, s, "::"))
            .{ .type = .@"::" }
        else if (std.mem.eql(u8, s, ".."))
            .{ .type = .@".." }
        else if (s[s.len - 1] == '=')
            .{ .type = .@"a=", .meta = s[0 .. s.len - 1] }
        else if (s[0] == '=')
            .{ .type = .@"=a", .meta = s[1..] }
        else if (s.len >= 2 and s[0] == '`' and s[s.len - 1] == '`')
            .{ .type = .@"inline", .meta = s[1 .. s.len - 1] }
        else
            .{ .type = .atom, .meta = s };
    }

    const Type = enum {
        __a,
        @"::",
        @"..",
        @"a=",
        @"=a",
        @"inline",
        atom,
    };
};

const RawTokenizer = struct {
    buf: []const u8,

    fn init(s: []const u8) RawTokenizer {
        return .{ .buf = s };
    }

    fn next(self: *RawTokenizer) ?[]const u8 {
        return while (self.buf.len > 0) {
            var i: usize = 0;
            defer self.buf = self.buf[@min(i + 1, self.buf.len)..];
            if (self.buf[0] == '`') {
                if (std.mem.indexOfScalarPos(u8, self.buf, 1, '`')) |r| {
                    i = r;
                    break self.buf[0 .. r + 1];
                }
            }
            while (i < self.buf.len) : (i += 1) {
                if (std.ascii.isWhitespace(self.buf[i]))
                    break;
            }
            if (i != 0) break self.buf[0..i];
        } else null;
    }
};

test "raw tokenizer" {
    const s =
        \\__foo a b ::
        \\a=    a
        \\      b
        \\`add a0, =a, a0`
        \\  =a
        \\..
    ;
    const expected = [_][]const u8{
        "__foo", "a",  "b", "::",
        "a=",    "a",  "b", "`add a0, =a, a0`",
        "=a",    "..",
    };
    var i: usize = 0;
    var iter = RawTokenizer.init(s);
    while (iter.next()) |raw| : (i += 1) {
        try std.testing.expect(i < expected.len);
        try std.testing.expectEqualStrings(expected[i], raw);
    }
    try std.testing.expectEqual(expected.len, i);
}

/// Lifetime of `s` must be not less than lifetime of function result.
fn tokenizeFromSlice(alloc: std.mem.Allocator, s: []const u8) ![]Token {
    var list = std.ArrayList(Token).init(alloc);
    var iter = RawTokenizer.init(s);
    while (iter.next()) |raw| {
        try list.append(Token.init(raw));
    }
    return list.toOwnedSlice();
}

test "tokenizer" {
    const prog =
        \\__foo a b ::
        \\a=    a
        \\      b
        \\`add a0, =a, a0`
        \\  =a
        \\..
    ;
    const alloc = std.testing.allocator;
    const tokens = try tokenizeFromSlice(alloc, prog);
    defer alloc.free(tokens);

    try std.testing.expectEqualDeep(&[_]Token{
        .{ .type = .__a, .meta = "foo" },
        .{ .type = .atom, .meta = "a" },
        .{ .type = .atom, .meta = "b" },
        .{ .type = .@"::" },
        .{ .type = .@"a=", .meta = "a" },
        .{ .type = .atom, .meta = "a" },
        .{ .type = .atom, .meta = "b" },
        .{ .type = .@"inline", .meta = "add a0, =a, a0" },
        .{ .type = .@"=a", .meta = "a" },
        .{ .type = .@".." },
    }, tokens);
}

pub const ParseError = std.mem.Allocator.Error || error{
    DuplicateArg,
    DuplicateSunc,
    DuplicateGlobalSunc,
    EOF,
    EmptyMeta,
    ExpectedExpr,
    ExpectedSuncDeclOrStmt,
    UnexpectedType,
    UnknownArg,
    UnknownSunc,
    UnknownTag,
};

const TokenReader = struct {
    tokens: []const Token,
    cur_idx: usize = 0,

    fn readExpected(self: *TokenReader, expected: Token.Type) !Token {
        const tok = try self.peek();
        if (tok.type != expected) return ParseError.UnexpectedType;
        defer self.cur_idx += 1;
        return tok;
    }

    fn readMetaExpected(self: *TokenReader, expected: Token.Type) ![]const u8 {
        const tok = try self.readExpected(expected);
        return tok.meta orelse ParseError.EmptyMeta;
    }

    fn peek(self: TokenReader) !Token {
        return if (self.isEmpty()) ParseError.EOF else self.tokens[self.cur_idx];
    }

    fn peekType(self: TokenReader) !Token.Type {
        return (try self.peek()).type;
    }

    fn isEmpty(self: TokenReader) bool {
        return self.cur_idx == self.tokens.len;
    }

    fn rollback(self: *TokenReader) void {
        self.cur_idx -= 1;
    }
};

const glob_sunc_name = "glob";

const ExecContext = struct {
    alloc: std.mem.Allocator,
    sunc_name: []const u8 = glob_sunc_name,

    fn init(alloc: std.mem.Allocator) ExecContext {
        return .{
            .alloc = alloc,
        };
    }

    fn getUid(self: ExecContext, uid: []const u8) ![]const u8 {
        return std.fmt.allocPrint(self.alloc, ".L{s}__{s}", .{ self.sunc_name, uid });
    }
};

pub fn compile(alloc: std.mem.Allocator, s: []const u8) ![]const u8 {
    const tokens = try tokenizeFromSlice(alloc, s);
    defer alloc.free(tokens);

    var arena = std.heap.ArenaAllocator.init(alloc);
    defer arena.deinit();

    const root = try buildASTLeaky(arena.allocator(), tokens);

    var ctx = ExecContext.init(arena.allocator());
    const source = try root.execute(arena.allocator(), &ctx);

    return alloc.dupe(u8, source); // source will be destroyed with arena
}

test "compile inline suffix" {
    const prog =
        \\ __iter a b ::
        \\ 0
        \\ `~a~:`
        \\  a
        \\ `bz a0, ~e~`
        \\  b
        \\ `j ~a~`
        \\ `~e~:`
        \\ ..
    ;

    const s = try compile(std.testing.allocator, prog);
    defer std.testing.allocator.free(s);
}

test "compile base" {
    const prog =
        \\ __+ a b ::
        \\ a=   a
        \\  b
        \\ `add a0, $a$, a0`
        \\ ..
        \\
        \\ __main ::
        \\ a=   + 13 + 8 -9
        \\  + 1 =a
        \\ ..
        \\
        \\ main
        \\ 0
    ;

    const s = try compile(std.testing.allocator, prog);
    defer std.testing.allocator.free(s);
}

fn buildASTLeaky(alloc: std.mem.Allocator, tokens: []const Token) !*const NodeRoot {
    var r: TokenReader = .{ .tokens = tokens };
    var ctx = ASTContext.init(alloc);
    return NodeRoot.init(alloc, &r, &ctx);
}

const ASTContext = struct {
    suncs: std.StringArrayHashMap(*const NodeSuncDecl),
    tags: std.StringArrayHashMap(void),
    args: std.StringArrayHashMap(void),

    fn init(alloc: std.mem.Allocator) ASTContext {
        return .{
            .suncs = std.StringArrayHashMap(*const NodeSuncDecl).init(alloc),
            .tags = std.StringArrayHashMap(void).init(alloc),
            .args = std.StringArrayHashMap(void).init(alloc),
        };
    }
};

const NodeRoot = struct {
    tops: []INodeTop,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *ASTContext) !*const NodeRoot {
        const node = try alloc.create(@This());
        var tops = std.ArrayList(INodeTop).init(alloc);
        while (!r.isEmpty()) {
            const top = try INodeTop.init(alloc, r, ctx);
            try tops.append(top);
        }

        node.* = .{ .tops = try tops.toOwnedSlice() };
        return node;
    }

    fn execute(self: NodeRoot, alloc: std.mem.Allocator, ctx: *ExecContext) ![]const u8 {
        // TODO: implement
        _ = self;
        _ = ctx;
        return std.fmt.allocPrint(alloc, "TODO: implement\n", .{});
    }
};

const INodeTop = union {
    sunc_decl: *const NodeSuncDecl,
    stmt: *const NodeStmt,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *ASTContext) !INodeTop {
        return if (NodeSuncDecl.init(alloc, r, ctx)) |sunc_decl|
            .{ .sunc_decl = sunc_decl }
        else |_| if (NodeStmt.init(alloc, r, ctx)) |stmt|
            .{ .stmt = stmt }
        else |_|
            ParseError.ExpectedSuncDeclOrStmt;
    }
};

const NodeSuncDecl = struct {
    name: []const u8,
    args: []*const NodeArgDecl,
    body: []*const NodeStmt,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *ASTContext) !*const NodeSuncDecl {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.__a);
        errdefer r.rollback();
        if (ctx.suncs.contains(name)) return ParseError.DuplicateSunc;
        if (std.mem.eql(u8, name, glob_sunc_name)) return ParseError.DuplicateGlobalSunc;

        var args = std.ArrayList(*const NodeArgDecl).init(alloc);
        ctx.args.clearRetainingCapacity();
        while (try r.peekType() != .@"::") {
            const arg = try NodeArgDecl.init(alloc, r, ctx);
            try args.append(arg);
        }
        _ = try r.readExpected(.@"::");

        var body = std.ArrayList(*const NodeStmt).init(alloc);
        ctx.tags.clearRetainingCapacity();
        while (try r.peekType() != .@"..") {
            const stmt = try NodeStmt.init(alloc, r, ctx);
            try body.append(stmt);
        }
        _ = try r.readExpected(.@"..");

        node.* = .{ .name = name, .args = try args.toOwnedSlice(), .body = try body.toOwnedSlice() };
        try ctx.suncs.putNoClobber(node.name, node);
        return node;
    }
};

const NodeArgDecl = struct {
    name: []const u8,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *ASTContext) !*const NodeArgDecl {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.atom);
        errdefer r.rollback();
        if (ctx.args.contains(name)) return ParseError.DuplicateArg;

        node.* = .{ .name = name };
        try ctx.args.putNoClobber(node.name, {});
        return node;
    }
};

const NodeArgPlace = struct {
    name: []const u8,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *const ASTContext) !*const NodeArgPlace {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.atom);
        errdefer r.rollback();
        if (!ctx.args.contains(name)) return ParseError.UnknownArg;

        node.* = .{ .name = name };
        return node;
    }
};

const NodeTagPlace = struct {
    name: []const u8,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *const ASTContext) !*const NodeTagPlace {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.@"=a");
        errdefer r.rollback();
        if (!ctx.tags.contains(name)) return ParseError.UnknownTag;

        node.* = .{ .name = name };
        return node;
    }
};

const NodeSuncPlace = struct {
    name: []const u8,
    args: []*const NodeStmt,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *const ASTContext) !*const NodeSuncPlace {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.atom);
        errdefer r.rollback();
        const sunc = ctx.suncs.get(name) orelse return ParseError.UnknownSunc;

        var args = std.ArrayList(*const NodeStmt).init(alloc);
        for (sunc.args) |_| {
            const stmt = try NodeStmt.init(alloc, r, ctx);
            try args.append(stmt);
        }

        node.* = .{ .name = name, .args = try args.toOwnedSlice() };
        return node;
    }
};

const NodeTagDecl = struct {
    name: []const u8,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *ASTContext) !*const NodeTagDecl {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.@"a=");
        errdefer r.rollback();

        node.* = .{ .name = name };
        try ctx.tags.put(node.name, {});
        return node;
    }
};

const NodeStmt = struct {
    tag: ?*const NodeTagDecl,
    expr: INodeExpr,
    @"inline": ?*const NodeInline,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *const ASTContext) ParseError!*const NodeStmt {
        const node = try alloc.create(@This());
        const tag = NodeTagDecl.init(alloc, r, @constCast(ctx)) catch null;

        const expr = try INodeExpr.init(alloc, r, ctx);

        const @"inline" = NodeInline.init(alloc, r, ctx) catch null;

        node.* = .{ .tag = tag, .expr = expr, .@"inline" = @"inline" };
        return node;
    }
};

const NodeLiteral = struct {
    value: i64,

    fn init(alloc: std.mem.Allocator, r: *TokenReader) !*const NodeLiteral {
        const node = try alloc.create(@This());
        const value = try r.readMetaExpected(.atom);
        errdefer r.rollback();

        node.* = .{ .value = try std.fmt.parseInt(i64, value, 0) };
        return node;
    }

    fn execute(self: NodeLiteral, alloc: std.mem.Allocator) ![]const u8 {
        return std.fmt.allocPrint(alloc, "li a0, {}\n", .{self.value});
    }
};

const INodeExpr = union(enum) {
    tag_place: *const NodeTagPlace,
    arg_place: *const NodeArgPlace,
    sunc_place: *const NodeSuncPlace,
    literal: *const NodeLiteral,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *const ASTContext) !INodeExpr {
        return if (NodeTagPlace.init(alloc, r, ctx)) |tag|
            .{ .tag_place = tag }
        else |_| if (NodeArgPlace.init(alloc, r, ctx)) |arg|
            .{ .arg_place = arg }
        else |_| if (NodeSuncPlace.init(alloc, r, ctx)) |sunc|
            .{ .sunc_place = sunc }
        else |_| if (NodeLiteral.init(alloc, r)) |literal|
            .{ .literal = literal }
        else |_|
            ParseError.ExpectedExpr;
    }
};

const NodeInline = struct {
    tmpl: []const u8,
    opts: []INodeTmplOpt,
    next_inline: ?*const NodeInline,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *const ASTContext) !*const NodeInline {
        const node = try alloc.create(@This());
        const tmpl = try r.readMetaExpected(.@"inline");
        errdefer r.rollback();

        var opts = std.ArrayList(INodeTmplOpt).init(alloc);
        var iter_uid = Extractor.init(tmpl, '~');
        while (iter_uid.next()) |raw| {
            const uid = try NodeTmplUId.init(alloc, raw);
            try opts.append(INodeTmplOpt.init(uid));
        }
        var iter_tag = Extractor.init(tmpl, '$');
        while (iter_tag.next()) |raw| {
            const tag = try NodeTmplTag.init(alloc, raw, ctx);
            try opts.append(INodeTmplOpt.init(tag));
        }

        const next_inline = NodeInline.init(alloc, r, ctx) catch null;

        node.* = .{ .tmpl = tmpl, .opts = try opts.toOwnedSlice(), .next_inline = next_inline };
        return node;
    }

    const Extractor = struct {
        iter: std.mem.SplitIterator(u8, .scalar),

        fn init(buf: []const u8, delim: u8) Extractor {
            return .{
                .iter = std.mem.splitScalar(u8, buf, delim),
            };
        }

        fn next(self: *Extractor) ?[]const u8 {
            return if (self.iter.next()) |_|
                if (self.iter.next()) |raw| raw else null
            else
                null;
        }
    };
};

const NodeTmplUId = struct {
    name: []const u8,

    fn init(alloc: std.mem.Allocator, raw: []const u8) !*const NodeTmplUId {
        const node = try alloc.create(@This());

        node.* = .{ .name = raw };
        return node;
    }
};

const NodeTmplTag = struct {
    name: []const u8,

    fn init(alloc: std.mem.Allocator, raw: []const u8, ctx: *const ASTContext) !*const NodeTmplTag {
        const node = try alloc.create(@This());
        if (!ctx.tags.contains(raw)) return ParseError.UnknownTag;

        node.* = .{ .name = raw };
        return node;
    }
};

const INodeTmplOpt = union(enum) {
    tmpl_uid: *const NodeTmplUId,
    tmpl_tag: *const NodeTmplTag,

    fn init(node: anytype) INodeTmplOpt {
        return switch (@TypeOf(node)) {
            *const NodeTmplUId => .{ .tmpl_uid = node },
            *const NodeTmplTag => .{ .tmpl_tag = node },
            else => @compileError("Unsupported struct type: " ++ @typeName(@TypeOf(node))),
        };
    }
};
