import system.io

variable [io.interface]

meta def main : io unit :=
  io.print $ to_string `(f x y)

