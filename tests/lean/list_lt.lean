#eval to_bool ([1, 2] < [2, 1])
#eval to_bool ([2, 1] < [1, 2])
#eval to_bool ("ab" < "ba")
#eval to_bool ("ba" < "ab")
#reduce to_bool ("ba" < "ab")
example : ¬ ("ba" < "ab") := dec_trivial
