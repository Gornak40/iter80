const std = @import("std");

const iter = @import("iter");

pub fn main() !void {
    var gpa: std.heap.GeneralPurposeAllocator(.{}) = .{};
    const alloc = gpa.allocator();

    const args = try std.process.argsAlloc(alloc);
    if (args.len != 2) {
        return error.UsageError; // TODO: more verbose
    }

    var file = try std.fs.cwd().openFile(args[1], .{});
    defer file.close();

    const source = try file.readToEndAlloc(alloc, std.math.maxInt(u32));
    defer alloc.free(source);

    const tokens = try iter.tokenizeFromSlice(alloc, source);
    defer alloc.free(tokens);
    std.debug.print("{any}\n", .{tokens});
}
