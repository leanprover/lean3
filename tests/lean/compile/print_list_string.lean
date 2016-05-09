import system.io

definition main : IO unit :=
    print_string (string_append "Hello" "Again!")
