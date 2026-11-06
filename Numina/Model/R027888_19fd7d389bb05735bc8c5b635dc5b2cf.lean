import Mathlib

theorem algebra_291579 : ⌊1 / Real.sqrt (16 - 6 * Real.sqrt 7)⌋ = 2 := by
  have h1 : Real.sqrt (16 - 6 * Real.sqrt 7) = 3 - Real.sqrt 7 := by
    have h2 : Real.sqrt (16 - 6 * Real.sqrt 7) = 3 - Real.sqrt 7 := by
      have h3 : (3 - Real.sqrt 7 : ℝ) ^ 2 = 16 - 6 * Real.sqrt 7 := by
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
      have h4 : 0 ≤ (3 - Real.sqrt 7 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_le_sqrt (show (7 : ℝ) ≤ (9 : ℝ) by norm_num)]
      rw [← h3]
      field_simp [Real.sqrt_sq h4]
    exact h2
  have h2 : (1 / Real.sqrt (16 - 6 * Real.sqrt 7) : ℝ) = (3 + Real.sqrt 7) / 2 := by
    rw [h1]
    have h3 : (3 - Real.sqrt 7 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_le_sqrt (show (7 : ℝ) ≤ (9 : ℝ) by norm_num)]
    field_simp [h3]
    <;> nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
  rw [h2]
  have h3 : 2 ≤ (3 + Real.sqrt 7) / 2 := by
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (7 : ℝ) by norm_num)]
  have h4 : (3 + Real.sqrt 7) / 2 < (3 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_le_sqrt (show (7 : ℝ) ≤ (9 : ℝ) by norm_num)]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> (try linarith)