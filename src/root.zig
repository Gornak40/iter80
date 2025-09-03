const std = @import("std");

const Token = struct {
    type: Type,
    meta: ?[]const u8 = null,

    fn init(s: []const u8) Token {
        return if (std.mem.startsWith(u8, s, "__"))
            .{ .type = .__a, .meta = s[2..] }
        else if (std.mem.startsWith(u8, s, "##"))
            .{ .type = .@"##a", .meta = s[2..] }
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
        @"##a",
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
    var list: std.ArrayListUnmanaged(Token) = .empty;
    var iter = RawTokenizer.init(s);
    while (iter.next()) |raw| {
        try list.append(alloc, Token.init(raw));
    }
    return list.toOwnedSlice(alloc);
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
    NotEnoughRegisters,
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
    options: CompileOptions,

    scope: Scope = .{},

    tag_manager: TagManager = .{},
    suncs: std.StringArrayHashMapUnmanaged(*const NodeSuncDecl) = .empty,

    const Scope = struct {
        name: []const u8 = glob_sunc_name,
        tags: std.StringArrayHashMapUnmanaged(TagManager.Register) = .empty,
        args: std.StringArrayHashMapUnmanaged([]const u8) = .empty,

        fn getUid(self: Scope, alloc: std.mem.Allocator, uid: []const u8) ![]const u8 {
            return std.fmt.allocPrint(alloc, ".L{s}__{s}", .{ self.name, uid });
        }
    };
};

const TagManager = struct {
    used: std.EnumSet(Register) = .initEmpty(),

    const Register = enum { s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, a7, a6, a5, a4, a3, a2, a1 };
    const registers = std.enums.values(Register);

    fn lock(self: *TagManager) ?Register {
        for (registers) |r| {
            if (!self.used.contains(r)) {
                self.used.toggle(r);
                return r;
            }
        }
        return null;
    }

    fn unlock(self: *TagManager, r: Register) void {
        self.used.remove(r);
    }
};

pub const CompileOptions = struct {
    label: []const u8 = "main",
    include: []const []const u8 = &.{},
};

pub fn compile(alloc: std.mem.Allocator, s: []const u8, options: CompileOptions) ![]const u8 {
    var arena = std.heap.ArenaAllocator.init(alloc);
    defer arena.deinit();

    const tokens = try tokenizeFromSlice(arena.allocator(), s);

    const root = try buildASTLeaky(arena.allocator(), tokens, options);

    var ctx: ExecContext = .{ .options = options };
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

    const s = try compile(std.testing.allocator, prog, .{});
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

    const s = try compile(std.testing.allocator, prog, .{});
    defer std.testing.allocator.free(s);
}

fn buildASTLeaky(alloc: std.mem.Allocator, tokens: []const Token, optinos: CompileOptions) !*const NodeRoot {
    var r: TokenReader = .{ .tokens = tokens };
    var ctx: ASTContext = .{ .options = optinos };
    return NodeRoot.init(alloc, &r, &ctx);
}

const ASTContext = struct {
    options: CompileOptions,

    suncs: std.StringArrayHashMapUnmanaged(*const NodeSuncDecl) = .empty,
    tags: std.StringArrayHashMapUnmanaged(void) = .empty,
    args: std.StringArrayHashMapUnmanaged(void) = .empty,
};

const NodeRoot = struct {
    tops: []INodeTop,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *ASTContext) !*const NodeRoot {
        const node = try alloc.create(@This());
        var tops: std.ArrayListUnmanaged(INodeTop) = .empty;
        while (!r.isEmpty()) {
            const top = try INodeTop.init(alloc, r, ctx);
            try tops.append(alloc, top);
        }

        node.* = .{ .tops = try tops.toOwnedSlice(alloc) };
        return node;
    }

    fn execute(self: NodeRoot, alloc: std.mem.Allocator, ctx: *ExecContext) ![]const u8 {
        var source: std.ArrayListUnmanaged(u8) = .empty;
        try std.fmt.format(source.writer(alloc), ".global {s}\n{s}:\n", .{ ctx.options.label, ctx.options.label });
        for (self.tops) |top| {
            switch (top) {
                .sunc_decl => |sunc_decl| {
                    try ctx.suncs.putNoClobber(alloc, sunc_decl.name, sunc_decl);
                },
                .stmt => |stmt| {
                    const part = try stmt.execute(alloc, ctx);
                    try source.appendSlice(alloc, part);
                },
            }
        }
        try std.fmt.format(source.writer(alloc), "ret\n", .{});
        return source.toOwnedSlice(alloc);
    }
};

const INodeTop = union(enum) {
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

        var args: std.ArrayListUnmanaged(*const NodeArgDecl) = .empty;
        ctx.args.clearRetainingCapacity();
        while (try r.peekType() != .@"::") {
            const arg = try NodeArgDecl.init(alloc, r, ctx);
            try args.append(alloc, arg);
        }
        _ = try r.readExpected(.@"::");

        var body: std.ArrayListUnmanaged(*const NodeStmt) = .empty;
        ctx.tags.clearRetainingCapacity();
        while (try r.peekType() != .@"..") {
            const stmt = try NodeStmt.init(alloc, r, ctx);
            try body.append(alloc, stmt);
        }
        _ = try r.readExpected(.@"..");

        node.* = .{ .name = name, .args = try args.toOwnedSlice(alloc), .body = try body.toOwnedSlice(alloc) };
        try ctx.suncs.putNoClobber(alloc, node.name, node);
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
        try ctx.args.putNoClobber(alloc, node.name, {});
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

    fn execute(self: NodeArgPlace, alloc: std.mem.Allocator, ctx: *const ExecContext) ![]const u8 {
        _ = alloc;
        return ctx.scope.args.get(self.name) orelse unreachable;
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

    fn execute(self: NodeTagPlace, alloc: std.mem.Allocator, ctx: *const ExecContext) ![]const u8 {
        const register = ctx.scope.tags.get(self.name) orelse unreachable;
        return std.fmt.allocPrint(alloc, "mv a0, {s}\n", .{@tagName(register)});
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

        var args: std.ArrayListUnmanaged(*const NodeStmt) = try .initCapacity(alloc, sunc.args.len);
        for (sunc.args) |_| {
            const stmt = try NodeStmt.init(alloc, r, ctx);
            args.appendAssumeCapacity(stmt);
        }

        node.* = .{ .name = name, .args = try args.toOwnedSlice(alloc) };
        return node;
    }

    fn execute(self: NodeSuncPlace, alloc: std.mem.Allocator, ctx: *ExecContext) ParseError![]const u8 {
        const sunc = ctx.suncs.get(self.name) orelse unreachable;
        var scope: ExecContext.Scope = .{ .name = sunc.name };
        for (sunc.args, self.args) |key, value| {
            const source = try value.execute(alloc, ctx);
            try scope.args.put(alloc, key.name, source);
        }

        std.mem.swap(ExecContext.Scope, &scope, &ctx.scope);
        defer std.mem.swap(ExecContext.Scope, &scope, &ctx.scope);
        defer for (ctx.scope.tags.values()) |r| ctx.tag_manager.unlock(r);

        var source: std.ArrayListUnmanaged(u8) = .empty;
        for (sunc.body) |stmt| {
            const part = try stmt.execute(alloc, ctx);
            try source.appendSlice(alloc, part);
        }
        return source.toOwnedSlice(alloc);
    }
};

const NodeTagDecl = struct {
    name: []const u8,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *ASTContext) !*const NodeTagDecl {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.@"a=");
        errdefer r.rollback();

        node.* = .{ .name = name };
        try ctx.tags.put(alloc, node.name, {});
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

    fn execute(self: NodeStmt, alloc: std.mem.Allocator, ctx: *ExecContext) ![]const u8 {
        var source: std.ArrayListUnmanaged(u8) = .empty;
        const part = switch (self.expr) {
            inline else => |expr| try expr.execute(alloc, ctx),
        };
        try source.appendSlice(alloc, part);
        if (self.tag) |tag| {
            const register = ctx.scope.tags.get(tag.name) orelse ctx.tag_manager.lock() orelse return ParseError.NotEnoughRegisters;
            try ctx.scope.tags.put(alloc, tag.name, register);
            try std.fmt.format(source.writer(alloc), "mv {s}, a0\n", .{@tagName(register)});
        }
        if (self.@"inline") |@"inline"| {
            const code = try @"inline".execute(alloc, ctx);
            try source.appendSlice(alloc, code);
        }
        return source.toOwnedSlice(alloc);
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

    fn execute(self: NodeLiteral, alloc: std.mem.Allocator, ctx: *const ExecContext) ![]const u8 {
        _ = ctx;
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
    parts: []Part,
    next_inline: ?*const NodeInline,

    const Part = union(enum) {
        raw: []const u8,
        uid: []const u8,
        tag: []const u8,
    };

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *const ASTContext) !*const NodeInline {
        const node = try alloc.create(@This());
        const tmpl = try r.readMetaExpected(.@"inline");
        errdefer r.rollback();

        const parts = try extractParts(alloc, tmpl);
        for (parts) |part| {
            switch (part) {
                .tag => |tag| if (!ctx.tags.contains(tag)) return ParseError.UnknownTag,
                else => continue,
            }
        }
        const next_inline = NodeInline.init(alloc, r, ctx) catch null;

        node.* = .{ .parts = parts, .next_inline = next_inline };
        return node;
    }

    fn extractParts(alloc: std.mem.Allocator, tmpl: []const u8) ![]Part {
        var parts: std.ArrayListUnmanaged(Part) = .empty;
        var i: usize = 0;
        while (i < tmpl.len) {
            var part: Part = undefined;
            if (std.mem.indexOfAnyPos(u8, tmpl, i + 1, "~$")) |j| {
                if (tmpl[i] == tmpl[j]) {
                    part = switch (tmpl[i]) {
                        '~' => .{ .uid = tmpl[i + 1 .. j] },
                        '$' => .{ .tag = tmpl[i + 1 .. j] },
                        else => unreachable,
                    };
                    i = j + 1;
                } else {
                    part = .{ .raw = tmpl[i..j] };
                    i = j;
                }
            } else {
                part = .{ .raw = tmpl[i..] };
                i = tmpl.len;
            }

            try parts.append(alloc, part);
        }

        return parts.toOwnedSlice(alloc);
    }

    fn execute(self: NodeInline, alloc: std.mem.Allocator, ctx: *ExecContext) ![]const u8 {
        var source: std.ArrayListUnmanaged(u8) = .empty;
        for (self.parts) |part| {
            const line = switch (part) {
                .raw => |raw| raw,
                .uid => |uid| try ctx.scope.getUid(alloc, uid),
                .tag => |tag| @tagName(ctx.scope.tags.get(tag) orelse unreachable),
            };
            try source.appendSlice(alloc, line);
        }
        try source.append(alloc, '\n');
        if (self.next_inline) |next_inline| {
            const next = try next_inline.execute(alloc, ctx);
            try source.appendSlice(alloc, next);
        }
        return source.toOwnedSlice(alloc);
    }
};

test "inline template parts" {
    const tmpl = "~label1~: ~label2~: $a$,$b$ $amogus$~label3~: abracadabra";
    const parts = try NodeInline.extractParts(std.testing.allocator, tmpl);
    defer std.testing.allocator.free(parts);

    const expected = &[_]NodeInline.Part{
        .{ .uid = "label1" },
        .{ .raw = ": " },
        .{ .uid = "label2" },
        .{ .raw = ": " },
        .{ .tag = "a" },
        .{ .raw = "," },
        .{ .tag = "b" },
        .{ .raw = " " },
        .{ .tag = "amogus" },
        .{ .uid = "label3" },
        .{ .raw = ": abracadabra" },
    };
    try std.testing.expectEqualDeep(expected, parts);
}
