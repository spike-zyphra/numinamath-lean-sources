import Mathlib

/-What is the simplified value of $\frac{\sqrt{24}}{\sqrt{30}}\div\frac{\sqrt{20}}{3\sqrt{25}}$?-/
theorem algebra_20263 : (Real.sqrt 24 / Real.sqrt 30) / (Real.sqrt 20 / (3 * Real.sqrt 25)) = 3 := by
  rw [show (24 : ℝ) = 2^2 * 6 by norm_num]
  rw [show (30 : ℝ) = 5 * 6 by norm_num]
  rw [show (20 : ℝ) = 2^2 * 5 by norm_num]
  rw [show (25 : ℝ) = 5^2 by norm_num]
  repeat rw [Real.sqrt_mul (by positivity)]
  repeat rw [Real.sqrt_sq (by norm_num)]
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by positivity)]
  ring_nf
