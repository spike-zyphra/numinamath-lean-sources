import Mathlib

theorem algebra_179669 : ∃ z : ℝ, z = Real.sqrt (192 + 96 * Real.sqrt 3) + Real.sqrt (192 - 96 * Real.sqrt 3) ∧ z = 24 := by
  use 24
  constructor
  · -- Show that 24 equals the given expression
    have h1 : Real.sqrt (192 + 96 * Real.sqrt 3) + Real.sqrt (192 - 96 * Real.sqrt 3) = (24 : ℝ) := by
      have h2 : Real.sqrt (192 + 96 * Real.sqrt 3) ≥ 0 := Real.sqrt_nonneg (192 + 96 * Real.sqrt 3)
      have h3 : Real.sqrt (192 - 96 * Real.sqrt 3) ≥ 0 := Real.sqrt_nonneg (192 - 96 * Real.sqrt 3)
      have h4 : (Real.sqrt (192 + 96 * Real.sqrt 3) + Real.sqrt (192 - 96 * Real.sqrt 3)) ^ 2 = (576 : ℝ) := by
        have h5 : Real.sqrt (192 + 96 * Real.sqrt 3) ^ 2 = (192 + 96 * Real.sqrt 3 : ℝ) := by
          rw [Real.sq_sqrt]
          nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
        have h6 : Real.sqrt (192 - 96 * Real.sqrt 3) ^ 2 = (192 - 96 * Real.sqrt 3 : ℝ) := by
          rw [Real.sq_sqrt]
          nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), sq_nonneg (Real.sqrt 3 - 2)]
        have h7 : Real.sqrt (192 + 96 * Real.sqrt 3) * Real.sqrt (192 - 96 * Real.sqrt 3) = (96 : ℝ) := by
          have h8 : Real.sqrt (192 + 96 * Real.sqrt 3) * Real.sqrt (192 - 96 * Real.sqrt 3) = Real.sqrt ((192 + 96 * Real.sqrt 3) * (192 - 96 * Real.sqrt 3)) := by
            rw [← Real.sqrt_mul (by
              nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
            )]
          rw [h8]
          have h9 : (192 + 96 * Real.sqrt 3) * (192 - 96 * Real.sqrt 3) = (9216 : ℝ) := by
            nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
          rw [h9]
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        calc
          (Real.sqrt (192 + 96 * Real.sqrt 3) + Real.sqrt (192 - 96 * Real.sqrt 3)) ^ 2
            = Real.sqrt (192 + 96 * Real.sqrt 3) ^ 2 + Real.sqrt (192 - 96 * Real.sqrt 3) ^ 2 + 2 * (Real.sqrt (192 + 96 * Real.sqrt 3) * Real.sqrt (192 - 96 * Real.sqrt 3)) := by ring
          _ = (192 + 96 * Real.sqrt 3) + (192 - 96 * Real.sqrt 3) + 2 * (96 : ℝ) := by
            rw [h5, h6, h7]
          _ = (576 : ℝ) := by
            nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
      have h8 : Real.sqrt (192 + 96 * Real.sqrt 3) + Real.sqrt (192 - 96 * Real.sqrt 3) ≥ 0 := by positivity
      have h3 : (24 : ℝ) ≥ 0 := by norm_num
      have h9 : Real.sqrt (192 + 96 * Real.sqrt 3) + Real.sqrt (192 - 96 * Real.sqrt 3) = (24 : ℝ) := by
        have h10 : (Real.sqrt (192 + 96 * Real.sqrt 3) + Real.sqrt (192 - 96 * Real.sqrt 3) : ℝ) ^ 2 = (24 : ℝ) ^ 2 := by
          rw [h4]
          all_goals norm_num
        have h11 : Real.sqrt (192 + 96 * Real.sqrt 3) + Real.sqrt (192 - 96 * Real.sqrt 3) ≥ 0 := by positivity
        have h12 : (24 : ℝ) ≥ 0 := by norm_num
        nlinarith [h10, h11, h12]
      exact h9
    linarith [h1]
  · -- Show z = 24
    norm_num