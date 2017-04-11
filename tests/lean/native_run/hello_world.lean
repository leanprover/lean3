import system.io

variable [io.interface]

-- set_option trace.compiler true

def main : io unit :=
    io.put_str "H"

#eval main
