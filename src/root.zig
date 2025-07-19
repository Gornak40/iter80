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
        .{ .type = .assembly, .meta = "add a0, =a, a0" },
        .{ .type = .@"=a", .meta = "a" },
        .{ .type = .@".." },
    }, tokens);
}

pub const ParseError = error{
    EOF,
    UnexpectedType,
    EmptyMeta,
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
    const r: TokenReader = .{ .tokens = tokens };
    return NodeRoot.init(alloc, r);
}

const NodeRoot = struct {
    suncs: []*const NodeSuncDecl,

    fn init(alloc: std.mem.Allocator, r: *TokenReader) !*const NodeRoot {
        const node = try alloc.create(@This());
        var suncs = std.ArrayList(*const NodeSuncDecl).init(alloc);
        while (!r.isEmpty()) {
            const sunc = try NodeSuncDecl.init(alloc, r);
            try suncs.append(sunc);
        }

        node.* = .{ .suncs = try suncs.toOwnedSlice() };
        return node;
    }
};

const NodeSuncDecl = struct {
    name: []const u8,
    args: []*const NodeArgDecl,
    body: []INodeStmt,

    fn init(alloc: std.mem.Allocator, r: *TokenReader) !*const NodeSuncDecl {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.__a);

        var args = std.ArrayList(*const NodeArgDecl).init(alloc);
        while (try r.peekType() != .@"::") {
            const arg = try NodeArgDecl.init(alloc, r);
            try args.append(arg);
        }
        _ = r.readExpected(.@"::");

        var body = std.ArrayList(INodeStmt).init(alloc);
        while (try r.peekType() != .@"..") {
            const arg = try INodeStmt.init(alloc, r);
            try body.append(arg);
        }
        _ = r.readExpected(.@"..");

        node.* = .{ .name = name, .args = try args.toOwnedSlice(), .body = try body.toOwnedSlice() };
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

    fn init(alloc: std.mem.Allocator, r: *TokenReader) !*const NodeArgPlace {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.atom);

        node.* = .{ .name = name };
        return node;
    }
};

const NodeTagPlace = struct {
    name: []const u8,

    fn init(alloc: std.mem.Allocator, r: *TokenReader) !*const NodeTagPlace {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.@"=a");

        node.* = .{ .name = name };
        return node;
    }
};

const NodeSuncPlace = struct {
    name: []const u8,
    args: []INodeExpr,

    fn init(alloc: std.mem.Allocator, r: *TokenReader) !*const NodeSuncPlace {
        const node = try alloc.create(@This());
        const name = try r.readMetaExpected(.atom);

        var args = std.ArrayList(INodeExpr).init(alloc);
        // TODO: read args

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

const NodeTaggedExpr = struct {
    tag: *const NodeTagDecl,
    expr: INodeExpr,

    fn init(alloc: std.mem.Allocator, r: *TokenReader) !*const NodeTaggedExpr {
        const node = try alloc.create(@This());
        const tag = try NodeTagDecl.init(alloc, r);

        const expr = try INodeExpr.init(alloc, r);

        node.* = .{ .tag = tag, .expr = expr };
        return node;
    }
};

const NodeInlineExpr = struct {
    @"inline": *const NodeInline,
    expr: INodeExpr,
};

const INodeStmt = union(enum) {
    expr: INodeExpr,
    tagged_expr: NodeTaggedExpr,
    inline_expr: NodeInlineExpr,
};

const INodeExpr = union(enum) {
    arg_place: *const NodeArgPlace,
    tag_place: *const NodeTagPlace,
    sunc_place: *const NodeSuncPlace,
};

const NodeInline = struct {
    tmpl: []const u8,
    opts: []INodeTmplOpt,
    next_inline: ?*const NodeInline,
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
