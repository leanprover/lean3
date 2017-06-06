
example : 1 + 2 = 3 :=
by change 2 + 1 = 3

example : 1 + 2 = 3 :=
by change 2 + 2 = 3

example (h : 1 + 2 = 3) : 2 + 2 = 4 :=
by change 2 + 1 = 3 at h

example (h : 1 + 2 = 3) : 2 + 2 = 4 :=
by change 2 + 1 = 3 at h h

example (h : 1 + 2 = 3) : 2 + 2 = 4 :=
by change 2 + 1 = 3 at *

example (h : 1 + 2 = 3) : 1 + 2 = 3 :=
by change 1 + 2 with 2 + 1 at h

example (h : 1 + 2 = 1 + 2 + 1) : 1 + 2 = 3 :=
by change 1 + 2 with 3 at *

example (h : 1 + 2 = 1 + 2 + 1) : 1 + 2 = 3 :=
by change 1 + 2 with 4 at *
