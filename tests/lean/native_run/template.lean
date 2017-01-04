import data.list
import system.io

inductive token
| string : string -> token
| var : string -> token

inductive template
| string : string -> template -> template
| interpolate : string -> template -> template
| empty : template

definition split_on' (c : char) : string -> list string
| "" := []
| (h :: tail) :=
    if h = c
    then "" :: split_on' tail
    else match split_on' tail with
    | [] := (h :: []) :: []
    | (curr :: rest) :=
        (h :: curr) :: rest
    end

def last {A : Type} : list A -> option A
| [] := none
| (x :: []) := some x
| (x :: xs) := last xs

def init {A : Type} : list A -> list A
| [] := []
| (x :: []) := []
| (x :: xs) := x :: init xs

def starts_with (c : char) (s : string) : bool :=
    match last s with
    | none := bool.ff
    | some fst :=
        if fst = c
        then bool.tt
        else bool.ff
    end

def split_on := fun c s, list.reverse $ split_on' c s

def to_token (s : string) : token :=
    if starts_with #"$" s
    then token.var (init s)
    else token.string s

def token.to_string : token -> string
| (token.var s) := "$" ++ s
| (token.string s) := s

instance : has_to_string token :=
    (| token.to_string |)

def template.to_string : template -> string
| (template.empty) := ""
| (template.string s t) := s ++ " " ++ template.to_string t
| (template.interpolate v t) := v ++ " " ++ template.to_string t

instance : has_to_string template :=
    (| template.to_string |)

def lex (s : string) : list token :=
    list.map to_token $ split_on #" " s

def parse : list token -> template
| [] := template.empty
| (token.var s :: ts) := template.interpolate s (parse ts)
| (token.string s :: ts) := template.string s (parse ts)

def env := list (prod string string)

def lookup (key : string) : env -> option string
| [] := none
| ((k', v) :: rest) :=
    if key = k'
    then some v
    else lookup rest

def render (e : env) : template -> string
| (template.empty) := ""
| (template.string s t) := s ++ " " ++ render t
| (template.interpolate var t) :=
    match lookup var e with
    | none := "error unknown variable: " ++ var
    | some val := val ++ " " ++ render t
    end

def to_template (s : string) : template :=
    parse (lex s)

def main : io unit :=
    put_str $ render [("name", "World"), ("year", "2017")] (to_template "Hello $name , see you next $year")

vm_eval main
