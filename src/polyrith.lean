import data.real.basic
import data.complex.basic
import system.io
import algebra
import tactic.linear_combination

open native tactic

namespace polyrith

-- # Poly Datatype

meta inductive poly
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

meta def const_fraction_parser : parser poly := do
  str "poly.const ",
  numer ← nat,
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
|(sum.inl s) := fail "parser didn't work"
|(sum.inr poly_list) := return poly_list

meta def convert_sage_output : string → tactic (list poly)
|s := (let sage_stuff := sage_output_parser.run_string (remove_trailing_whitespace s) in trace ("|" ++ remove_trailing_whitespace s ++ "|") >> parser_output_checker (sage_stuff))

constant x:ℚ
run_cmd let sg := "(poly.var 2) (poly.const 1/1) " in convert_sage_output sg >>= list.mmap (poly.to_pexpr [(`(x), 2)]) >>= list.mmap to_expr >>= trace

#eval poly_parser.run_string "(poly.pow (poly.var 4) 5)"
#eval poly_parser.run_string "(poly.mul (poly.const 1/1) (poly.mul (poly.var 1) (poly.mul (poly.var 1) (poly.mul (poly.var 1) (poly.var 1)))))"
#eval poly_parser.run_string "(poly.mul (poly.const 3/4) (poly.var 0))"
#eval poly_parser.run_string "(poly.sum (poly.mul (poly.const 1/1) (poly.mul (poly.var 1) (poly.mul (poly.var 1) (poly.mul (poly.var 1) (poly.var 1))))) (poly.sum (poly.mul (poly.const 7/1) (poly.mul (poly.var 1) (poly.mul (poly.var 0) (poly.var 0)))) (poly.mul (poly.const 3/4) (poly.var 0))))"
#eval sage_output_parser.run_string "(poly.const 1/1) (poly.const 1/1) "
run_cmd poly.to_pexpr [(`(x), 0)] (poly.mul (poly.const (5/3)) (poly.var 0)) >>= to_expr >>= trace

local notation `reduc` := transparency.reducible

meta def equality_to_left_side : expr → tactic expr 
| `(%%lhs = %%rhs) := 
  do 
    out_expr ← to_expr ``(%%lhs - %%rhs),
    return out_expr
| e := fail "expression is not an equality"

-- run_cmd equality_to_left_side `(4 = 5)

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


-- |expt `(@eq %%R _ _) := 
-- (do unify expt R, return tt) <|> return ff
-- |expt e := return ff

meta def get_equalities_of_type : expr → list expr → tactic (list expr)
| expt l := l.mfilter (is_eq_of_type expt)

-- constants (x y : ℤ) (z : ℚ)
-- run_cmd get_equalities_of_type `(ℤ) [`(x=5)] >>= trace

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
let args := ["src/test.py"] ++ arg_list in
do
  s ← tactic.unsafe_run_io $ io.cmd { cmd := "python3", args := args},
  return s

meta def get_var_names : exmap → list string
| [] := []
| ((e, n) :: tl) := ("var" ++ to_string n) :: (get_var_names tl)


-- # main tactic

meta def polyrith : tactic unit :=
do
  (m, p, R) ← parse_target_to_poly,
  (eq_names, m, polys) ← parse_ctx_to_polys R m,
  trace $ polys.mmap (poly.to_pexpr m) >>= mmap to_expr,
  trace eq_names,
  sage_out ← sage_output [to_string R, (get_var_names m).to_string, (polys.map poly.mk_string).to_string, p.mk_string],
  coeffs_as_poly ← convert_sage_output sage_out,
  coeffs_as_pexpr ← coeffs_as_poly.mmap (poly.to_pexpr m),
  linear_combo.linear_combination (eq_names.map expr.local_pp_name) coeffs_as_pexpr

constant p : ℚ → Prop 
constants (R : Type) [inst_R : comm_ring R] [inst_R_sub : has_sub R]
example (x y z: ℚ) (h: x + y = 0) (h1 : x^2 = 0): 2*x + 2*y = 0 :=
begin 
    polyrith, 
    assumption,
end
end polyrith
