import polyrith

constant p : ℚ → Prop 
constants (R : Type) [inst_R : comm_ring R]

constant term : ∀ a b : ℚ, a + b = 0
-- set_option trace.polyrith true

example (a b c d : ℚ) (h : a + b = 0) (h2 : c + d = 0) (h3 : c + a = 0): c + a + d + b = 0 :=
begin 
  linear_combination h + h2
end 

-- set_option trace.polyrith true

example (x y z: ℤ) (h: x + y = 0) (h1 : x^2 = 0): 4*x^3*y^2 + x^2*y^2 + x*y^3 = 0 :=
begin 
  linear_combination y ^ 2 * x * h + 4 * (y ^ 2 * x) * h1,
end

-- theorem T
--   (a b x1 y1 x2 y2 x4 y4 :ℚ )
--   (A :y1*y1-x1*x1*x1-a*x1-b = 0)
--   (B :y2*y2-x2*x2*x2-a*x2-b = 0)
--   (C :y4*y4-x4*x4*x4-a*x4-b = 0)
--   {i3:ℚ} (Hi3:i3*(x2-x1)-1=0)
--   {k3:ℚ} (Hk3:(y2-y1)*i3-k3=0)
--   {x3:ℚ} (Hx3:k3*k3-x1-x2-x3=0)
--   {y3:ℚ} (Hy3:k3*(x1-x3)-y1-y3=0)
--   {i7:ℚ} (Hi7:i7*(x4-x3)-1=0)
--   {k7:ℚ} (Hk7:(y4-y3)*i7-k7=0)
--   {x7:ℚ} (Hx7:k7*k7-x3-x4-x7=0)
--   {y7:ℚ} (Hy7:k7*(x3-x7)-y3-y7=0)
--   {i6:ℚ} (Hi6:i6*(x4-x2)-1=0)
--   {k6:ℚ} (Hk6:(y4-y2)*i6-k6=0)
--   {x6:ℚ} (Hx6:k6*k6-x2-x4-x6=0)
--   {y6:ℚ} (Hy6:k6*(x2-x6)-y2-y6=0)
--   {i9:ℚ} (Hi9:i9*(x6-x1)-1=0)
--   {k9:ℚ} (Hk9:(y6-y1)*i9-k9=0)
--   {x9:ℚ} (Hx9:k9*k9-x1-x6-x9=0)
--   {y9:ℚ} (Hy9:k9*(x1-x9)-y1-y9=0)
--   : x9 - x7 = 0 ∧ y9 - y7 = 0 :=
-- begin 
--   split, sorry, sorry,
-- end

example {K : Type*} [field K] [invertible 2] [invertible 3]
  {ω p q r s t x: K} (hp_nonzero : p ≠ 0) (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r)
  (ht : t * s = p) (x : K) (H : 1 + ω + ω ^ 2 = 0) : 
  x ^ 3 + 3 * p * x - 2 * q =
    (x - (s - t)) * (x - (s * ω - t * ω ^ 2)) * (x - (s * ω ^ 2 - t * ω)) :=
begin
  have hs_nonzero : s ≠ 0,
  { contrapose! hp_nonzero with hs_nonzero,
    linear_combination -1 * ht + t * hs_nonzero,
     },
  have H' : 2 * q = s ^ 3 - t ^ 3,
  { rw ← mul_left_inj' (pow_ne_zero 3 hs_nonzero),
    linear_combination -1 * hr + ((-1) * s ^ 3 + (-1) * r + q) * hs3 + (t ^ 2 * s ^ 2 + p * t * s + p ^ 2) * ht,},
  linear_combination (ω ^ 4 * t + (-1) * (ω ^ 4 * s) + ω ^ 4 * x + ω ^ 3 * t + (-1) * (ω ^ 3 * s) +
          ω ^ 2 * t +
        (-1) * (ω ^ 2 * s) +
      3 * (ω ^ 2 * x) +
    2 * (ω * x)) * ht + ((-1) * (ω * t ^ 3) + ω * s ^ 3 + ω ^ 2 * t * p + (-1) * (ω ^ 2 * s * p) +
                    (-1) * (ω * t ^ 2 * x) +
                  (-1) * (ω * s ^ 2 * x) +
                ω ^ 2 * p * x +
              t ^ 3 +
            (-1) * s ^ 3 +
          (-1) * (ω * p * x) +
        (-1) * (t * x ^ 2) +
      s * x ^ 2 +
    3 * (p * x)) * H + -1 * H',
end
