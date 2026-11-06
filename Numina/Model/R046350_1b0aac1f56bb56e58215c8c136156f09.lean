import Mathlib

theorem algebra_316307 : IsGreatest {x | ∃ t : ℝ, x = 4 * (Real.cos t)^3 - 3 * (Real.cos t)^2 - 6 * Real.cos t + 5} (27 / 4) := by
  constructor
  · -- Show that 27/4 is in the image of the function
    use Real.arccos (-1 / 2)
    have h : Real.cos (Real.arccos (-1 / 2)) = -1 / 2 := by 
      apply Real.cos_arccos
      norm_num
      norm_num
    rw [h]
    norm_num
    <;> nlinarith
  · -- Show that 27/4 is the greatest value in the image
    intro x hx
    rcases hx with ⟨t, ht⟩
    rw [ht]
    have h1 : -1 ≤ Real.cos t ∧ Real.cos t ≤ 1 := by
      constructor
      · -- Show -1 ≤ Real.cos t
        linarith [Real.neg_one_le_cos t]
      · -- Show Real.cos t ≤ 1
        linarith [Real.cos_le_one t]
    nlinarith [sq_nonneg (Real.cos t + 1 / 2), sq_nonneg (Real.cos t - 1), 
      sq_nonneg (Real.cos t + 1), sq_nonneg (Real.cos t - 1 / 2), 
      sq_nonneg (Real.cos t ^ 2 - 1 / 4), 
      sq_nonneg (Real.cos t + 1 / 2), sq_nonneg (Real.cos t - 1 / 2), 
      Real.cos_le_one t, Real.neg_one_le_cos t, 
      mul_nonneg (show (0 : ℝ) ≤ 1 - Real.cos t by nlinarith) 
        (show (0 : ℝ) ≤ Real.cos t + 1 by nlinarith)
    ]