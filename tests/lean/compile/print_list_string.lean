import system.io

definition is_empty (s : string) : string :=
    string.cases_on s "empty" (fun x y, "non-empty")

definition main : IO unit :=
    print_string (trace "app" (string_append "" "Hello"))
