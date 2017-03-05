import system.io

def main :=
  let xs : list nat := [1,2,3] in
  put_str_ln $ list.map (fun x, x + 1) xs
