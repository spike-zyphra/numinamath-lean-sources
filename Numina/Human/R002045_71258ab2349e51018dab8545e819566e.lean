import Mathlib

/- Let $f\left(x\right)=x^2-14x+52$ and $g\left(x\right)=ax+b$, where $a$ and $b$ are positive. Find $a$, given that $f\left(g\left(-5\right)\right)=3$ and $f\left(g\left(0\right)\right)=103$.

$\text{(A) }2\qquad\text{(B) }5\qquad\text{(C) }7\qquad\text{(D) }10\qquad\text{(E) }17$ -/
theorem algebra_58993 {f g : ℝ → ℝ} (hf : f = fun x => x ^ 2 - 14 * x + 52)
    (hg : ∀ x, g x = a * x + b) (ha : 0 < a) (hb : 0 < b)
    (h1 : f (g (-5)) = 3) (h2 : f (g 0) = 103) :
    a = 2 := by 
  -- simplify the problem according to the definitions of f and g
  simp_all
  -- use code form convertibility arithmetic
  nlinarith [sq_nonneg (a - 2)]