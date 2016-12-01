meta def procedure :=
  name × expr

meta def procedure.to_string : procedure → string
| (n, e) := "def " ++ to_string n ++ " := \n" ++ to_string e

meta def procedure.map_body (f : expr → expr) : procedure → procedure
| (n, e) := (n, f e)

meta instance : has_to_string procedure :=
  (| procedure.to_string |)
