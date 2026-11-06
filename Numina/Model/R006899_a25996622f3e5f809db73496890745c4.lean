import Mathlib

theorem algebra_18913 : IsGreatest {t : ℤ | t > 60 ∧ 70 * t - (t - 60) * t > 4200} 69 := by
  constructor
  · -- Verify that 69 is in the set
    constructor
    · -- Show that 69 > 60
      norm_num
    · -- Verify the inequality for 69
      norm_num
  · -- Show that 69 is the greatest element in the set
    intro t ht
    rcases ht with ⟨ht1, ht2⟩
    by_contra h
    push_neg at h
    have h1 : t ≥ 70 := by omega
    nlinarith [sq_nonneg ((t : ℤ) - 60), sq_nonneg ((t : ℤ) - 70)]