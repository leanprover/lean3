
example (n m : ℕ) : n + m = m + n :=
begin
let s := n + m,
induction n,
case nat.zero : {sorry}, -- error: could not find open goal of given case
case nat.succ : {sorry}
end
