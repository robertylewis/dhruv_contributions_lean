import data.real.basic
import data.complex.basic
import system.io
import algebra
import tactic.linear_combination

open native tactic

namespace polyrith

-- # Poly Datatype

inductive poly
|const: ℚ → poly 
|var: ℕ → poly
|add: poly → poly → poly
|mul: poly → poly → poly

meta def poly.mk_string : poly → string
| (poly.const z) := to_string z
| (poly.var n) := "var" ++ to_string n
| (poly.add p q) := "(" ++ poly.mk_string p ++ " + " ++ poly.mk_string q ++ ")"
| (poly.mul p q) := "(" ++ poly.mk_string p ++ " * " ++ poly.mk_string q ++ ")"

@[reducible] meta def poly.pow : poly → ℕ → poly
| _ 0 := poly.const 1
| p 1 := p
| p (nat.succ n) := poly.mul p (poly.pow p n)

meta instance : has_add poly := ⟨poly.add⟩ 
meta instance : has_mul poly := ⟨poly.mul⟩
meta instance : has_pow poly ℕ := ⟨poly.pow⟩ 
meta instance : has_repr poly := ⟨poly.mk_string⟩  
meta instance : has_to_format poly := ⟨to_fmt ∘ poly.mk_string⟩  

-- # Parsing algorithms
local notation `exmap` := list (expr × ℕ)

meta def poly_form_of_atom (red : transparency) (m : exmap) (e : expr) : tactic (exmap × poly) :=
(do (_, k) ← m.find_defeq red e, return (m, poly.var k)) <|>
(let n := m.length + 1 in return ((e, n)::m, poly.var n))

meta def poly_form_of_expr (red : transparency) : exmap → expr → tactic (exmap × poly)
| m `(%%e1 * %%e2) :=
   do (m', comp1) ← poly_form_of_expr m e1,
      (m', comp2) ← poly_form_of_expr m' e2,
      return (m', comp1 * comp2)
| m `(%%e1 + %%e2) :=
   do (m', comp1) ← poly_form_of_expr m e1,
      (m', comp2) ← poly_form_of_expr m' e2,
      return (m', comp1 + comp2)
| m `(%%e1 - %%e2) :=
   do (m', comp1) ← poly_form_of_expr m e1,
      (m', comp2) ← poly_form_of_expr m' e2,
      return (m',  comp1 + ((poly.const (-1)) * comp2))
| m `(-%%e) := 
  do (m', comp) ← poly_form_of_expr m e,
     return (m', (poly.const (-1)) * comp)
| m p@`(@has_pow.pow _ ℕ _ %%e %%n) :=
  match n.to_nat with
  | some k :=
    do (m', comp) ← poly_form_of_expr m e,
    return (m', comp^k)
  | none := poly_form_of_atom red m p
  end
| m e :=
  match e.to_rat with
  | some z := return ⟨m, poly.const z⟩
  | none := poly_form_of_atom red m e
  end

meta def has_val: ℕ → (expr × ℕ) → tactic unit
| n (_,m) := unify `(n) `(m)


meta def poly.to_pexpr :exmap → poly → tactic pexpr
| _ (poly.const z) := return $  ``(%%z)
| m (poly.var n) := 
  do
    (e, num) ← m.mfind (has_val n),
    return ``(%%e)
| m (poly.add p q) := 
  do 
    p_pexpr ← poly.to_pexpr m p,
    q_pexpr ← poly.to_pexpr m q,
    return ``(%%p_pexpr + %%q_pexpr)
| m (poly.mul p q) := 
  do 
    p_pexpr ← poly.to_pexpr m p,
    q_pexpr ← poly.to_pexpr m q,
    return ``(%%p_pexpr * %%q_pexpr)

-- # Parsing sage output to poly
open parser
meta def var_parser : parser poly := do
  str "poly.var ",
  n ← nat,
  return (poly.var n)

meta def neg_nat_parser : parser int := do
  ch '-',
  n ← nat,
  return (- n)

meta def nat_as_int_parser : parser int := do
  n ← nat,
  return (n)

meta def const_fraction_parser : parser poly := do
  str "poly.const ",
  numer ← neg_nat_parser <|> nat_as_int_parser,
  ch '/',
  denom ← nat,
  return (poly.const (numer/denom))

meta def add_parser (cont : parser poly) : parser poly := do
  str "poly.sum ",
  lhs ← cont,
  ch ' ',
  rhs ← cont,
  return (poly.add lhs rhs)

meta def mul_parser (cont : parser poly) : parser poly := do
  str "poly.mul ",
  lhs ← cont,
  ch ' ',
  rhs ← cont,
  return (poly.mul lhs rhs)

meta def pow_parser (cont : parser poly) : parser poly := do
  str "poly.pow ",
  base ← cont,
  ch ' ',
  n ← nat,
  return (poly.pow base n)

meta def poly_parser : parser poly := do
  ch '(',
  t ←  var_parser <|> const_fraction_parser <|> add_parser poly_parser 
    <|> mul_parser poly_parser <|> pow_parser poly_parser,
  ch ')',
  return t

meta def one_of_many_poly_parser : parser poly := do
  p ← poly_parser,
  optional $ ch ' ',
  return p

@[derive decidable]
meta def _root_.char.is_whitespace' (c : char) : Prop :=
c.is_whitespace ∨ c.to_nat = 13

meta def remove_trailing_whitespace : string → string 
| s := if s.back.is_whitespace' then remove_trailing_whitespace s.pop_back else s

meta def sage_output_parser : parser (list poly) := do
  poly_list ← many (one_of_many_poly_parser),
  return poly_list

meta def parser_output_checker : string ⊕ (list poly) → tactic (list poly) 
|(sum.inl s) := fail "poly parser didn't work - likely a bad output from sage"
|(sum.inr poly_list) := return poly_list

meta def convert_sage_output : string → tactic (list poly)
|s := (let sage_stuff := sage_output_parser.run_string (remove_trailing_whitespace s) in parser_output_checker sage_stuff)

-- constants x y :ℚ
-- run_cmd let sg := "(poly.sum (poly.mul (poly.const -4/1) (poly.mul (poly.var 1) (poly.mul (poly.var 1) (poly.mul (poly.var 1) (poly.var 1))))) (poly.mul (poly.const 1/1) (poly.mul (poly.var 1) (poly.mul (poly.var 2) (poly.var 2)))))" in 
-- convert_sage_output sg >>= list.mmap (poly.to_pexpr [(`(x), 1), (`(y), 2)]) >>= list.mmap to_expr >>= trace

local notation `reduc` := transparency.reducible

meta def equality_to_left_side : expr → tactic expr 
| `(%%lhs = %%rhs) := 
  do 
    out_expr ← to_expr ``(%%lhs - %%rhs),
    return out_expr
| e := fail "expression is not an equality"

meta def parse_target_to_poly : tactic (exmap × poly × expr) :=
do 
  e@`(@eq %%R _ _) ← target,
  left_side ← equality_to_left_side e,
  (m, p) ← poly_form_of_expr reduc [] left_side,
  return (m, p, R)

meta def fold_function (expt : expr):  (exmap × list poly) → expr → tactic (exmap × list poly)
| (m, poly_list) new_exp := 
do 
  (m', new_poly) ← poly_form_of_expr reduc m new_exp,
  return (m', poly_list ++ [new_poly])

meta def is_eq_of_type : expr → expr → tactic bool
| expt h_eq := (do `(@eq %%R _ _) ← infer_type h_eq, unify expt R, return tt) <|> return ff

meta def get_equalities_of_type : expr → list expr → tactic (list expr)
| expt l := l.mfilter (is_eq_of_type expt)

meta def parse_ctx_to_polys : expr → exmap → tactic (list expr × exmap × list poly)
| expt m :=
do
  ctx ← tactic.local_context,
  eq_names ← get_equalities_of_type expt ctx,
  eqs ← eq_names.mmap infer_type,
  eqs_to_left ← eqs.mmap equality_to_left_side,
  (m, poly_list) ← mfoldl (fold_function expt) (m, []) eqs_to_left,
  return (eq_names, m, poly_list)

-- # Connecting with Python
meta def sage_output (arg_list : list string := []) : tactic string :=
let args := ["src/test2.py"] ++ arg_list in
do
  s ← tactic.unsafe_run_io $ io.cmd { cmd := "python3", args := args},
  return s

meta def get_var_names : exmap → list string
| [] := []
| ((e, n) :: tl) := ("var" ++ to_string n) :: (get_var_names tl)

#check complex.I 
#check complex.I_sq
example : complex.I * complex.I = -1 :=
by ring_nf; simp only [complex.I_sq]; ring

-- # main tactic

meta def polyrith : tactic unit :=
do
  sleep 10, -- can lead to weird errors when actively editing code with polyrith calls
  (m, p, R) ← parse_target_to_poly,
  (eq_names, m, polys) ← parse_ctx_to_polys R m,
  -- trace $ polys.mmap (poly.to_pexpr m) >>= mmap to_expr,
  -- trace R, 
  -- trace $ get_var_names m, 
  -- trace (polys.map poly.mk_string),
  -- trace p.mk_string,
  sage_out ← sage_output [to_string R, (get_var_names m).to_string, (polys.map poly.mk_string).to_string, p.mk_string],
  trace sage_out,
  coeffs_as_poly ← convert_sage_output sage_out,
  coeffs_as_pexpr ← coeffs_as_poly.mmap (poly.to_pexpr m),
  let eq_names := eq_names.map expr.local_pp_name,  
  coeffs_as_expr ← coeffs_as_pexpr.mmap $ λ e, to_expr ``(%%e : %%R),
  -- trace coeffs_as_expr,
  expr_string ← (eq_names.zip coeffs_as_expr).mfoldl (λ s p, do ps ← tactic.pp p, return $ s ++ " " ++ to_string ps) "",
  linear_combo.linear_combination eq_names coeffs_as_pexpr,
  trace!"Try this: linear_combination{expr_string}"

constant p : ℚ → Prop 
constants (R : Type) [inst_R : comm_ring R]

example (a b c d : ℚ) (h : a + b = 0) (h2 : c + d = 0) : c + a + d + b = 0 :=
begin 
  linear_combination (h, 1) (h2, 1),
end 

example (x y z: ℚ) (h: x + y = 0) (h1 : x^2 = 0): 4*x^3*y^2 + x^2*y^2 + x*y^3 = 0 :=
begin 
    linear_combination (h, 4 * (y * (x * (x * x))) + ((-4) * (x * (x * (x * x))) + 1 * (x * (y * y)))) (h1, 4 * (x * (x * x))),
end

theorem T
  (a b x1 y1 x2 y2 x4 y4 :ℚ )
  (A :y1*y1-x1*x1*x1-a*x1-b = 0)
  (B :y2*y2-x2*x2*x2-a*x2-b = 0)
  (C :y4*y4-x4*x4*x4-a*x4-b = 0)
  {i3:ℚ} (Hi3:i3*(x2-x1)-1=0)
  {k3:ℚ} (Hk3:(y2-y1)*i3-k3=0)
  {x3:ℚ} (Hx3:k3*k3-x1-x2-x3=0)
  {y3:ℚ} (Hy3:k3*(x1-x3)-y1-y3=0)
  {i7:ℚ} (Hi7:i7*(x4-x3)-1=0)
  {k7:ℚ} (Hk7:(y4-y3)*i7-k7=0)
  {x7:ℚ} (Hx7:k7*k7-x3-x4-x7=0)
  {y7:ℚ} (Hy7:k7*(x3-x7)-y3-y7=0)
  {i6:ℚ} (Hi6:i6*(x4-x2)-1=0)
  {k6:ℚ} (Hk6:(y4-y2)*i6-k6=0)
  {x6:ℚ} (Hx6:k6*k6-x2-x4-x6=0)
  {y6:ℚ} (Hy6:k6*(x2-x6)-y2-y6=0)
  {i9:ℚ} (Hi9:i9*(x6-x1)-1=0)
  {k9:ℚ} (Hk9:(y6-y1)*i9-k9=0)
  {x9:ℚ} (Hx9:k9*k9-x1-x6-x9=0)
  {y9:ℚ} (Hy9:k9*(x1-x9)-y1-y9=0)
  : x9 - x7 = 0 ∧ y9 - y7 = 0 :=
begin 
  split, sorry, sorry,
end

theorem TT
  (a b x1 y1 x2 y2 x4 y4 :ℚ )
  (A :y1*y1-x1*x1*x1-a*x1-b = 0)
  (B :y2*y2-x2*x2*x2-a*x2-b = 0)
  (C :y4*y4-x4*x4*x4-a*x4-b = 0)
  {i3:ℚ} (Hi3:i3*(x2-x1)-1=0)
  {k3:ℚ} (Hk3:(y2-y1)*i3-k3=0)
  {x3:ℚ} 
  {y3:ℚ} 
  {i7:ℚ} 
  {k7:ℚ} 
  {x7:ℚ} (Hx7:k7*k7-x3-x4-x7=0)
  {y7:ℚ} (Hy7:k7*(x3-x7)-y3-y7=0)
  {i6:ℚ} 
  {k6:ℚ} 
  {x6:ℚ} 
  {y6:ℚ} 
  {i9:ℚ} (Hi9:i9*(x6-x1)-1=0)
  {k9:ℚ} (Hk9:(y6-y1)*i9-k9=0)
  {x9:ℚ} (Hx9:k9*k9-x1-x6-x9=0)
  {y9:ℚ} (Hy9:k9*(x1-x9)-y1-y9=0)
  : x9 - x7 = 0 ∧ y9 - y7 = 0 :=
begin 
  split, 
  polyrith,
end

end polyrith