(*
import("util.lua")
local ps   = proof_state()
local env  = environment()
local Bool = Const("Bool")
env:add_var("p", Bool)
env:add_var("q", Bool)
local p, q = Consts("p, q")
local ctx  = context()
ctx = ctx:extend("H1", p)
ctx = ctx:extend("H2", q)
ps  = to_proof_state(env, ctx, p)
print(ps)

S1 = State()
S2 = State()
x = 10
function tst_fn(env, ios, s)
   x = x + 1
   print(x)
   return s
end
t = tactic(tst_fn)
S1:dostring([[ x = 20; t, ps = ... ]], t, ps)
S2:dostring([[ x = 20; t, ps = ... ]], t, ps)
T1 = thread(S1, [[
    local ios = io_state()
    local env = environment()
    for i = 1, 10 do
    for s in t(env, ios, ps) do
       print("s1")
       print(s)
    end
    end
   ]])
T2 = thread(S2, [[
    local ios = io_state()
    local env = environment()
    for i = 1, 10 do
    for s in t(env, ios, ps) do
       print("s2")
       print(s)
    end
    end
   ]])
T1:wait()
T2:wait()
*)



