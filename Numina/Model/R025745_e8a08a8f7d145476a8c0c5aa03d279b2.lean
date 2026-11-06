import Mathlib

open Real

/- Simplify: $\frac{\sqrt{23-6\sqrt{6-4\sqrt{2}}}}{3+\sqrt{2}}=$ ___          ___. -/
theorem algebra_1676 : 0 < 6 - 4 * sqrt 2 ∧ 0 < 23 - 6 * sqrt (6 - 4 * sqrt 2) →
    sqrt (23 - 6 * sqrt (6 - 4 * sqrt 2)) / (3 + sqrt 2) = 1 := by
  intro h
  rcases h with ⟨h1, h2⟩
  have h3 : sqrt (6 - 4 * sqrt 2) = 2 - Real.sqrt 2 := by
    have h4 : (6 - 4 * Real.sqrt 2 : ℝ) = (Real.sqrt 2 - 2) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h4]
    have h5 : Real.sqrt ((Real.sqrt 2 - 2) ^ 2) = abs (Real.sqrt 2 - 2) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h5]
    have h6 : Real.sqrt 2 < (2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - 1.414)]
    have h7 : abs (Real.sqrt 2 - 2) = (2 - Real.sqrt 2) := by
      rw [abs_of_neg]
      linarith
      all_goals linarith
    rw [h7]
  have h8 : (23 - 6 * Real.sqrt (6 - 4 * Real.sqrt 2) : ℝ) = (11 + 6 * Real.sqrt 2) := by
    rw [h3]
    nlinarith
  have h9 : Real.sqrt (23 - 6 * Real.sqrt (6 - 4 * Real.sqrt 2) ) = 3 + Real.sqrt 2 := by
    rw [h8]
    have h10 : Real.sqrt (11 + 6 * Real.sqrt 2) = (3 + Real.sqrt 2) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    exact h10
  rw [h9]
  have h11 : (3 + Real.sqrt 2) / (3 + Real.sqrt 2) = 1 := by
    field_simp [show 3 + Real.sqrt 2 ≠ 0 by
      have h5 : Real.sqrt 2 > 0 := by
        apply Real.sqrt_pos.mpr
        all_goals norm_num
      linarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), h5]
      ]
  linarith [h11, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]