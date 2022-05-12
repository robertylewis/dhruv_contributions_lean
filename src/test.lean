-- import tactic.linarith
import polyrith
--## examples

<<<<<<< Updated upstream
=======
-- set_option trace.polyrith true
>>>>>>> Stashed changes

constant term : ∀ a b : ℚ, a + b = 0 
-- (h : a + b = 0)
example (a b c d : ℚ) (h1 : a + b = 0) (h2 : c + d = 0) (h3 : a + c = 0) (h4 : b + d = 0): c + a + d + b = 0 :=
begin 
  polyrith only [h1, term a b],
end 

<<<<<<< Updated upstream
example (x y z: ℚ) (h: x + y = 0) (h1 : x^2 = 0): 4*x^3*y^2 + x^2*y^2 = -x*y^3 :=
begin 
    linear_combination (h, 1 * (x * (y * y))) (h1, 4 * (x * (y * y))),
=======
constant term : ∀ a b : ℚ, a + b = 0 
-- (h : a + b = 0)
example (a b c d : ℚ) (h1 : a + b = 0) (h2 : c + d = 0) (h3 : a + c = 0) (h4 : b + d = 0): c + a + d + b = 0 :=
begin 
  linear_combination (h1, 1) (h2, 1),
end 

example (x y z: ℚ) (h: x + y = 0) (h1 : x^2 = 0): 4*x^3*y^2 + x^2*y^2 = -x*y^3 :=
begin 
    linear_combination (h, y ^ 2 * x) (h1, 4 * (y ^ 2 * x)),
>>>>>>> Stashed changes
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
  split, 
  {sorry},
  {sorry,}
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
  sorry, sorry,
end
