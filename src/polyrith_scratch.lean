import .conlib 
import system.io
import data.buffer.parser
import data.list.defs

#check tactic.linarith
#check tactic.interactive.linear_combination

meta def cmd_line_output : tactic unit :=
let args := ["src/test.py"] in
do
  s ← tactic.unsafe_run_io $ io.cmd { cmd := "python3", args := args},
  trace s return ()

run_cmd cmd_line_output


example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) (hd : even 2):
  -3*x - 3*y - 4*z = 2 :=
by linear_combination (ha, 1) (hb, -1) (hc, -2)

#check tactic.trace
#check tactic.pp

example (x y : ℚ) (h1 : x^2 + y = 0) (h2 : x*y + 4*x^2 = 0): x^3 + x*y = 0 :=
by linear_combination (h2, 1/16*y + 1) (h1, x - 1/4*y - 4)

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
  x*x*y + y*x*y + 6*x = 3*x*y + 14 :=
begin --linear_combination (h1, x*y) (h2, 2)
  {do 
    tactic.trace "local context:",
    ctx  ← tactic.local_context,
    tactic.trace ctx,
    types ← list.mmap tactic.infer_type ctx,
    types_formats ← list.mmap tactic.pp types,
    tactic.trace $ list.map to_string types_formats},
  linear_combination (h1, x*y) (h2, 2),
end


example (x y : ℚ) (h1 : x^2 * y - 1 = 0) (h2 : x * y^2 - x = 0) :
  x^4*y^2 - x^2*y + 3*x*y^2 - 3*x = 0 := 
by linear_combination (h2, 3) (h1, x^2 * y)
 
open io tactic

def mk_cmd (sage_cmd : string) : io.process.spawn_args :=
{ cmd := "curl",
  args := [
    "-X",
    "POST",
    "-H Content-Type: application/x-www-form-urlencoded",
    "--data-urlencode",
    "code="++sage_cmd,
    "https://sagecell.sagemath.org/service",
    "-s"
  ]}

meta def extract_result : json → tactic json 
| (json.object l) := prod.snd <$> (l.mfind $ λ pr, if prod.fst pr = "stdout" then return () else failed)
| _ := fail "not an object"

meta def extract_string : json → tactic string 
| (json.of_string s) := return s 
| _ := fail "not a string"

meta def sage_run (sage_cmd : string) : tactic string :=
do s ← unsafe_run_io $ cmd (mk_cmd sage_cmd),
   js ← json.parse s <|> fail "couldn't parse response",
   extract_result js >>= extract_string

-- note the use of the weird "string block" syntax: this is a string that could contain quotation marks
def sage_program : string :=
/-"

x,y,z = CC['x,y,z'].gens()
I = ideal(x^5 + y^4 + z^3 - 1,  x^3 + y^3 + z^2 - 1)
print(I.groebner_basis())

"-/

#eval sage_run sage_program >>= trace


meta def compute_gcd (a b : ℕ) : tactic ℕ :=
let cmd := sformat!"print(gcd({a}, {b}))" in do 
s ← sage_run cmd, 
sum.inr v ← return $ parser.nat.run_string s.pop_back,
return v

run_cmd compute_gcd 55 5 >>= trace

