import Mathlib

theorem algebra_193630 {a : ℝ} (ha : ∀ t, (2 * t + 1) ∣ (4 * t ^ 2 + 12 * t + a)) :
    a = 5 := by
  have h1 := ha (-1 / 2)
  norm_num at h1
  all_goals linarith