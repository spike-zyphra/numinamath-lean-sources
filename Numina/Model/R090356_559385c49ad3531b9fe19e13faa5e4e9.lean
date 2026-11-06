import Mathlib

theorem algebra_109529 (f : ℝ → ℝ) (hf : f = fun x => (x^8 + x^6 + x^4 + x^2 + 1) / (x^4 + x^3 + x^2 + x + 1)) :
    f (-0.02) = 312499999 / 306250000 := by
  rw [hf]
  norm_num
  <;> norm_num