import Mathlib

theorem algebra_187204 : Real.sqrt (4 + Real.sqrt 12) - Real.sqrt (4 - Real.sqrt 12) = 2 := by
  have h1 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  
  have h2 : Real.sqrt (4 + Real.sqrt 12) = Real.sqrt 3 + 1 := by
    rw [h1]
    have h3 : Real.sqrt (4 + 2 * Real.sqrt 3) = Real.sqrt 3 + 1 := by
      have h4 : (Real.sqrt 3 + 1) ^ 2 = 4 + 2 * Real.sqrt 3 := by
        calc
          (Real.sqrt 3 + 1) ^ 2 = (Real.sqrt 3) ^ 2 + 2 * Real.sqrt 3 + 1 := by ring
          _ = 3 + 2 * Real.sqrt 3 + 1 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
          _ = 4 + 2 * Real.sqrt 3 := by ring
      have h6 : 0 ≤ (Real.sqrt 3 + 1 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      rw [←h4]
      field_simp [Real.sqrt_sq h6]
    linarith [h3]

  have h3 : Real.sqrt (4 - Real.sqrt 12) = Real.sqrt 3 - 1 := by
    rw [h1]
    have h7 : Real.sqrt (4 - 2 * Real.sqrt 3) = Real.sqrt 3 - 1 := by
      have h8 : (Real.sqrt 3 - 1) ^ 2 = 4 - 2 * Real.sqrt 3 := by
        calc
          (Real.sqrt 3 - 1) ^ 2 = (Real.sqrt 3) ^ 2 - 2 * Real.sqrt 3 + 1 := by ring
          _ = 3 - 2 * Real.sqrt 3 + 1 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
          _ = 4 - 2 * Real.sqrt 3 := by ring
      have h4 : 1 < Real.sqrt 3 := by
        rw [Real.lt_sqrt] <;> norm_num
        <;> linarith [show (0 : ℝ) < (3 : ℝ) by norm_num]
      have h10 : 0 ≤ (Real.sqrt 3 - 1 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), h4]
      rw [←h8]
      field_simp [Real.sqrt_sq h10]
    linarith [h7]

  rw [h2, h3]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]