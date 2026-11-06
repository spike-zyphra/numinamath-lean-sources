import Mathlib

theorem algebra_197693 : ∃ n : ℕ, Real.sqrt (11 + 6 * Real.sqrt 2) + Real.sqrt (11 - 6 * Real.sqrt 2) = n := by
  use 6
  have h1 : Real.sqrt (11 + 6 * Real.sqrt 2) = 3 + Real.sqrt 2 := by
    have h2 : (3 + Real.sqrt 2) ^ 2 = 11 + 6 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h3 : 0 ≤ (3 + Real.sqrt 2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2]
    rw [← h2]
    field_simp [Real.sqrt_sq h3]
  have h4 : Real.sqrt (11 - 6 * Real.sqrt 2) = 3 - Real.sqrt 2 := by
    have h5 : (3 - Real.sqrt 2) ^ 2 = 11 - 6 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    have h6 : 0 ≤ (3 - Real.sqrt 2 : ℝ) := by
      have h7 : Real.sqrt 2 < (3 : ℝ) := by
        have h8 : Real.sqrt 2 < (3 : ℝ) := by
          rw [Real.sqrt_lt] <;> norm_num
          all_goals norm_num
          all_goals try { linarith [Real.sqrt_nonneg 2] }
          all_goals nlinarith [Real.sqrt_nonneg 2]
        linarith
      nlinarith [Real.sqrt_nonneg 2, h7]
    rw [← h5]
    field_simp [Real.sqrt_sq (show (0 : ℝ) ≤ (3 - Real.sqrt 2 : ℝ) by linarith [h6]) ]
  rw [h1, h4]
  ring_nf
  <;> norm_num
  <;> ring_nf <;> norm_num