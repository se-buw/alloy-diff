sig Red {} sig Green {} sig Blue {}
fact { not (some disj w, x, y, z: Red + Green + Blue | w = w) }
