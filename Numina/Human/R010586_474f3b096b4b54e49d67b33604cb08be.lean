import Mathlib

/- The sum of three numbers $a$, $b$, and $c$ is 99. If we increase $a$ by 6, decrease $b$ by 6 and multiply $c$ by 5, the three resulting numbers are equal. What is the value of $b$? -/
theorem algebra_14048 {a b c : ℝ} (h₀ : a + b + c = 99) (h₁ : a + 6 = b - 6) (h₂ : b - 6 = 5 * c) :
    b = 51 := by
  nlinarith
