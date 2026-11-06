import Mathlib

theorem algebra_1638 :
  (¬(∀ x y : ℝ, 4 * (x - 7) = 6 * (5 - 27 * x) → 6 * (5 - 27 * y) = 4 * (y - 7))) := by
  intro h
  specialize h (29 / 83 : ℝ) (0 : ℝ) (by norm_num)
  norm_num at h ⊢