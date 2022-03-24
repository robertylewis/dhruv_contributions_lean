import data.buffer.parser

inductive arith_expr
| atom : ℕ → arith_expr
| add : arith_expr → arith_expr → arith_expr
| mul : arith_expr → arith_expr → arith_expr


open arith_expr parser


def arith_expr.repr : arith_expr → string
| (atom n) := to_string n
| (add s t) := sformat!"({s.repr}) + ({t.repr})"
| (mul s t) := sformat!"({s.repr}) * ({t.repr})"

instance : has_repr arith_expr := ⟨arith_expr.repr⟩

-- grammar : "(var 0)", "(add (var 0) (var 2))", etc
-- note: we make assumptions about "one and only one space", can be relaxed if needed by using:
#check many (ch ' ')


def parse_atom : parser arith_expr := do
  str "var ",
  n ← nat,
  return (atom n)

section

-- `cont` is a "continuation," telling how to recursively parse arith_epxrs
variable (cont : parser arith_expr)

def parse_add : parser arith_expr := do
  str "add ",
  lhs ← cont,
  ch ' ',
  rhs ← cont,
  return (add lhs rhs)

def parse_mul : parser arith_expr := do
  str "mul ",
  lhs ← cont,
  ch ' ',
  rhs ← cont,
  return (mul lhs rhs)

end

meta def arith_parser : parser arith_expr := do
  ch '(',
  t ← parse_atom <|> parse_add arith_parser <|> parse_mul arith_parser,
  ch ')',
  return t

#eval arith_parser.run_string "(var 4)"
#check arith_parser.run_string "(add (var 4) (var 19))"