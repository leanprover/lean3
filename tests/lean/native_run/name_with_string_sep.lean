import system.io

variable [io.interface]

def main :=
    io.put_str $ name.to_string_with_sep "_" $ `a.b.c
