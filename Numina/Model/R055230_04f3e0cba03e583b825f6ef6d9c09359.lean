import Mathlib

theorem algebra_13788 (n : ℝ) : (5 : ℝ)^(2 * n + 1) = 1 / 25 ↔ n = -3 / 2 := by
  constructor
  · -- Assume (5 : ℝ)^(2 * n + 1) = 1 / 25, prove n = -3 / 2
    intro h
    have h1 : (5 : ℝ) ^ (2 * n + 1) = 1 / 25 := h
    have h2 : (5 : ℝ) ^ (2 * n + 1) = (5 : ℝ) ^ (-2 : ℝ) := by
      rw [h1]
      norm_num
      all_goals norm_num
    have h3 : 2 * n + 1 = -2 := by
      apply_fun (Real.logb (5 : ℝ)) at h2
      simp at h2
      all_goals linarith
    linarith
  · -- Assume n = -3 / 2, prove (5 : ℝ)^(2 * n + 1) = 1 / 25
    intro h
    rw [h]
    norm_num
    all_goals norm_num