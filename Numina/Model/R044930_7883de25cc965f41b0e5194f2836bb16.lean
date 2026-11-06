import Mathlib

open Real Set
open scoped Real

theorem algebra_238539 : IsGreatest {x | ∃ t, x = sin t ^ 2 * (1 + cos t)} (32/27) := by
  constructor
  · -- Show that 32/27 is in the set
    use (Real.arccos (1 / 3))
    have h1 : sin (Real.arccos (1 / 3)) ^ 2 = 1 - cos (Real.arccos (1 / 3)) ^ 2 := by
      have h2 : sin (Real.arccos (1 / 3)) ^ 2 + cos (Real.arccos (1 / 3)) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq (Real.arccos (1 / 3))
      have h3 : sin (Real.arccos (1 / 3)) ^ 2 = 1 - cos (Real.arccos (1 / 3)) ^ 2 := by
        linarith
      exact h3
    have h2 : cos (Real.arccos (1 / 3)) = 1 / 3 := by
      apply Real.cos_arccos
      all_goals norm_num
    rw [show sin (Real.arccos (1 / 3)) ^ 2 = 8 / 9 by
      rw [h1, h2]
      norm_num
    ]
    rw [show 1 + cos (Real.arccos (1 / 3)) = 4 / 3 by
      rw [h2]
      norm_num
    ]
    norm_num
  · -- Show that for all x in the set, x ≤ 32/27
    intro x hx
    rcases hx with ⟨t, ht⟩
    have ht2 : sin t ^ 2 = 1 - cos t ^ 2 := by
      have h1 : sin t ^ 2 + cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
      linarith
    rw [ht2] at ht
    have h7 : (1 - cos t ^ 2) * (1 + cos t) ≤ 32 / 27 := by
      have h1 : -1 ≤ cos t := Real.neg_one_le_cos t
      have h2 : cos t ≤ 1 := Real.cos_le_one t
      nlinarith [sq_nonneg (cos t - 1 / 3), sq_nonneg (cos t + 1), sq_nonneg (cos t - 1), sq_nonneg (cos t ^ 2 - 1 / 9), sq_nonneg (cos t ^ 2 - 1), sq_nonneg (cos t ^ 2 - (1 - cos t ^ 2)), Real.sin_sq_add_cos_sq t, Real.cos_le_one t, Real.neg_one_le_cos t]
    linarith