import Mathlib

open Real

theorem number_theory_7360 {n : ℕ} (hn : n = 4) :
    ∃ m : ℕ, m > 0 ∧ (1 + sqrt 2)^n = sqrt m + sqrt (m + 1) := by 
  rw [hn]
  use 288
  constructor
  · -- Show that 288 > 0
    norm_num
  · -- Show the equality
    have h5 : (1 + Real.sqrt 2) ^ 4 = 17 + 12 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h6 : Real.sqrt (288 : ℝ) = 12 * Real.sqrt 2 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h7 : Real.sqrt (288 + 1 : ℝ) = 17 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h8 : Real.sqrt (288 : ℝ) + Real.sqrt (288 + 1 : ℝ) = 17 + 12 * Real.sqrt 2 := by
      rw [h6, h7]
      all_goals linarith 
    have h9 : (1 + Real.sqrt 2 : ℝ) ^4 = Real.sqrt (288 : ℝ) + Real.sqrt (288 + 1 : ℝ) := by 
      linarith [h5, h8]
    simpa using h9