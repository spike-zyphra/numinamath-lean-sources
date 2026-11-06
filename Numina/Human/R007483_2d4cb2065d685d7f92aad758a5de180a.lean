import Mathlib

/- Use the Horner's method to calculate the value of the polynomial $f(x) = 4x^6 + 3x^5 + 4x^4 + 2x^3 + 5x^2 - 7x + 9$ at $x = 4$. -/
theorem algebra_9435 {f : ℝ → ℝ} (hf : f = fun x => 4 * x ^ 6 + 3 * x ^ 5 + 4 * x ^ 4 + 2 * x ^ 3 + 5 * x ^ 2 - 7 * x + 9) :
    f 4 = 20669 := by
  -- Horner's Rule
  have h (x : ℝ) : 4 * x ^ 6 + 3 * x ^ 5 + 4 * x ^ 4 + 2 * x ^ 3 + 5 * x ^ 2 - 7 * x + 9 = (((((4 * x + 3) * x + 4) * x + 2) * x + 5) * x - 7) * x + 9 := by ring
  simp [hf, h]
  norm_num
