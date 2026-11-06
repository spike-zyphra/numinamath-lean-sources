import Mathlib

/- Suppose that for some $a,b,c$ we have $a+b+c = 6$, $ab+ac+bc = 5$ and $abc = -12$. What is $a^3+b^3+c^3$? -/
theorem algebra_11354 {a b c : ℝ} (h₀ : a + b + c = 6) (h₁ : a * b + a * c + b * c = 5)
    (h₂ : a * b * c = -12) :
    a ^ 3 + b ^ 3 + c ^ 3 = 90 := by
  have h₃ : (a + b + c) ^ 2 = 36 := by nlinarith
  nlinarith
  <;> nlinarith