import Mathlib

/- Suppose that for some $a,b,c$ we have $a+b+c = 1$, $ab+ac+bc = abc = -4$. What is $a^3+b^3+c^3$? -/
theorem algebra_13096 {a b c : ℝ} (h₀ : a + b + c = 1) (h₁ : a * b + a * c + b * c = -4)
    (h₂ : a * b * c = -4) :
    a ^ 3 + b ^ 3 + c ^ 3 = 1 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]