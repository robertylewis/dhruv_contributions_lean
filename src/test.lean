import polyrith

constant term : ∀ a b : ℚ, a + b = 0

example (a b c d : ℚ) (h : a + b = 0) (h2 : c + d = 0) (h3 : c + a = 0): a + b + c + d = 0 :=
begin 
  polyrith,
end 

example (x y z: ℤ) (h: x + y = 0) (h1 : x^2 = 0): 4*x^3*y^2 + x^2*y^2 + x*y^3 = 0 :=
begin 
  polyrith,
end

example {K : Type*} [field K] [invertible 2] [invertible 3]
  {ω p q r s t x: K} (hp_nonzero : p ≠ 0) (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r)
  (ht : t * s = p) (x : K) (H : 1 + ω + ω ^ 2 = 0) : 
  x ^ 3 + 3 * p * x - 2 * q =
    (x - (s - t)) * (x - (s * ω - t * ω ^ 2)) * (x - (s * ω ^ 2 - t * ω)) :=
begin
  have hs_nonzero : s ≠ 0,
  { contrapose! hp_nonzero with hs_nonzero,
    polyrith,
     },
  have H' : 2 * q = s ^ 3 - t ^ 3,
  { rw ← mul_left_inj' (pow_ne_zero 3 hs_nonzero),
    polyrith,},
  polyrith,
end

set_option trace.polyrith true

example (a b c d : ℚ) (h : a + b = 0) (h2 : c + d = 0) (h3 : c + a = 0): a + b + c + d = 0 :=
begin 
  polyrith,
end 
