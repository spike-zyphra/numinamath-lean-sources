import Mathlib

theorem algebra_169872 (v1 v2 : ℝ) (h1 : v1 = 36 * 1000 / 3600) (h2 : v2 = 54 * 1000 / 3600)
    (h3 : ∃ t, t = 2 ∧ v2 * t > v1 * t + 40) :
    v2 * 2 > v1 * 2 + 42.5 := by
  rcases h3 with ⟨t, ht1, ht2⟩
  rw [ht1] at ht2
  rw [h1, h2] at ht2
  norm_num at ht2 ⊢
  all_goals linarith