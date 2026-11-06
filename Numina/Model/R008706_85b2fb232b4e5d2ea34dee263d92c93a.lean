import Mathlib

theorem algebra_10651 (h : ℝ → ℝ) (h_def : h = fun t => -16 * t ^ 2 - 24 * t + 160) :
    IsLeast {t | 0 ≤ t ∧ h t = 0} 2.5 := by 
  constructor
  · -- Verify 2.5 is in the set.
    constructor
    · norm_num
    · -- Show h 2.5 = 0
      rw [h_def]
      norm_num
  · -- Verify that 2.5 is the smallest element in the set.
    intro t ht
    rcases ht with ⟨ht_nonneg, ht_zero⟩
    rw [h_def] at ht_zero
    simp at ht_zero
    nlinarith [sq_nonneg (t - 2.5), sq_nonneg (t + 4)]