const std = @import("std");
const testing = std.testing;

test "basic add functionality" {
    try testing.expectEqual(3, 1 + 2);
}
