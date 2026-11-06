import Mathlib

theorem algebra_21780 : IsLeast {t : ℝ | t > 0 ∧ -6 * t ^ 2 + 43 * t = 77} 3.5 := by
  constructor
  · -- Show that 3.5 is in the set
    constructor
    · -- Verify that 3.5 > 0
      norm_num
    · -- Verify that -6 * (3.5)^2 + 43 * 3.5 = 77
      norm_num
  · -- Show that 3.5 is the least element in the set
    intro t ht
    rcases ht with ⟨ht_pos, heq⟩
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (t - 3.5), sq_nonneg (t - 11 / 3), sq_nonneg (t * 6), sq_nonneg (t - 3.5), sq_nonneg (t - 11 / 3), sq_nonneg (t * 6)]