import system.io

variable [io.interface]

def main : io unit :=
  let xs : list nat := [1,2,3] in
  io.print $ list.map (fun x, x + 1) xs

