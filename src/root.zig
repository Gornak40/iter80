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

/// Lifetime of `s` must be not less than lifetime of function result.
pub fn tokenizeFromSlice(alloc: std.mem.Allocator, s: []const u8) ![]Token {
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
    EOF,
    UnexpectedType,
    EmptyMeta,
    DuplicateSunc,
    UnknownSunc,
    ExpectedExpr,
};

const TokenReader = struct {
    tokens: []const Token,

    fn readExpected(self: *TokenReader, expected: Token.Type) !Token {
        const tok = try self.peek();
        if (tok.type != expected) return ParseError.UnexpectedType;
        defer self.tokens = self.tokens[1..];
        return tok;
    }

    fn readMetaExpected(self: *TokenReader, expected: Token.Type) ![]const u8 {
        const tok = try self.readExpected(expected);
        return tok.meta orelse ParseError.EmptyMeta;
    }

    fn peek(self: TokenReader) !Token {
        return if (self.isEmpty()) ParseError.EOF else self.tokens[0];
    }

    fn peekType(self: TokenReader) !Token.Type {
        return (try self.peek()).type;
    }

    fn isEmpty(self: TokenReader) bool {
        return self.tokens.len == 0;
    }
};

pub fn buildASTLeaky(alloc: std.mem.Allocator, tokens: []const Token) !*const NodeRoot {
    var r: TokenReader = .{ .tokens = tokens };
    var ctx = ASTContext.init(alloc);
    return NodeRoot.init(alloc, &r, &ctx);
}

test "build AST" {
    const tokens = [_]Token{};
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    _ = try buildASTLeaky(arena.allocator(), &tokens);
}

const ASTContext = struct {
    suncs: std.StringArrayHashMap(*const NodeSuncDecl),

    fn init(alloc: std.mem.Allocator) ASTContext {
        return .{
            .suncs = std.StringArrayHashMap(*const NodeSuncDecl).init(alloc),
        };
    }
};

const NodeRoot = struct {
    suncs: []*const NodeSuncDecl,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *ASTContext) !*const NodeRoot {
        const node = try alloc.create(@This());
        var suncs = std.ArrayList(*const NodeSuncDecl).init(alloc);
        while (!r.isEmpty()) {
            const sunc = try NodeSuncDecl.init(alloc, r, ctx);
            try suncs.append(sunc);
        }

        node.* = .{ .suncs = try suncs.toOwnedSlice() };
        return node;
    }
};

const NodeSuncDecl = struct {
    name: []const u8,
    args: []*const NodeArgDecl,
    body: []*const NodeStmt,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *ASTContext) !*const NodeSuncDecl {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.__a);
        if (ctx.suncs.get(name)) |_| {} else return ParseError.DuplicateSunc;

        var args = std.ArrayList(*const NodeArgDecl).init(alloc);
        while (try r.peekType() != .@"::") {
            const stmt = try NodeArgDecl.init(alloc, r);
            try args.append(stmt);
        }
        _ = try r.readExpected(.@"::");

        var body = std.ArrayList(*const NodeStmt).init(alloc);
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

    fn init(alloc: std.mem.Allocator, r: *TokenReader) !*const NodeArgDecl {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.atom);

        node.* = .{ .name = name };
        return node;
    }
};

const NodeArgPlace = struct {
    name: []const u8,

    // TODO: check if arg exists.
    fn init(alloc: std.mem.Allocator, r: *TokenReader) !*const NodeArgPlace {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.atom);

        node.* = .{ .name = name };
        return node;
    }
};

const NodeTagPlace = struct {
    name: []const u8,

    // TODO: check if tag exists.
    fn init(alloc: std.mem.Allocator, r: *TokenReader) !*const NodeTagPlace {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.@"=a");

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

    fn init(alloc: std.mem.Allocator, r: *TokenReader) !*const NodeTagDecl {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.@"a=");

        node.* = .{ .name = name };
        return node;
    }
};

const NodeStmt = struct {
    tag: ?*const NodeTagDecl,
    expr: INodeExpr,
    @"inline": ?*const NodeInline,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *const ASTContext) ParseError!*const NodeStmt {
        const node = try alloc.create(@This());
        const tag = NodeTagDecl.init(alloc, r) catch null;

        const expr = try INodeExpr.init(alloc, r, ctx);

        const @"inline" = NodeInline.init(alloc, r) catch null;

        node.* = .{ .tag = tag, .expr = expr, .@"inline" = @"inline" };
        return node;
    }
};

const NodeLiteral = struct {
    value: i64,

    fn init(alloc: std.mem.Allocator, r: *TokenReader) !*const NodeLiteral {
        const node = try alloc.create(@This());
        const value = try r.readMetaExpected(.atom);

        node.* = .{ .value = try std.fmt.parseInt(i64, value, 0) };
        return node;
    }
};

const INodeExpr = union(enum) {
    tag_place: *const NodeTagPlace,
    arg_place: *const NodeArgPlace,
    sunc_place: *const NodeSuncPlace,
    literal: *const NodeLiteral,

    fn init(alloc: std.mem.Allocator, r: *TokenReader, ctx: *const ASTContext) !INodeExpr {
        return if (NodeTagPlace.init(alloc, r)) |tag|
            .{ .tag_place = tag }
        else |_| if (NodeArgPlace.init(alloc, r)) |arg|
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

    fn init(alloc: std.mem.Allocator, r: *TokenReader) !*const NodeInline {
        const node = try alloc.create(@This());
        const tmpl = try r.readMetaExpected(.@"inline");

        var opts = std.ArrayList(INodeTmplOpt).init(alloc);
        // TODO: parse template, extract uids and tags.

        const next_inline = NodeInline.init(alloc, r) catch null;

        node.* = .{ .tmpl = tmpl, .opts = try opts.toOwnedSlice(), .next_inline = next_inline };
        return node;
    }
};

const NodeTmplUId = struct {
    name: []const u8,
};

const NodeTmplTag = struct {
    name: []const u8,
};

const INodeTmplOpt = union(enum) {
    tmpl_uid: *const NodeTmplUId,
    tmpl_tag: *const NodeTmplTag,
};
