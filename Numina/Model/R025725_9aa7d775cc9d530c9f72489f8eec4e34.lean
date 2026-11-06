import Mathlib

theorem algebra_11889 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a^2 + b^2 = 1) (m : ℝ) (h1 : a^3 + b^3 + 1 = m * (a + b + 1)^3) :
    (3 * Real.sqrt 2 - 4) / 2 ≤ m ∧ m < 1 / 4 := by
  have h4 : (3 * Real.sqrt 2 - 4) / 2 ≤ m := by
    have h_eq : m = (a^3 + b^3 + 1) / (a + b + 1)^3 := by
      field_simp [(show (a + b + 1 : ℝ) ≠ 0 by 
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, h]
      )]
      linarith [h1]
    rw [h_eq]
    have h5 : 0 < (a + b + 1 : ℝ) := by
      nlinarith
    have h6 : (a^3 + b^3 + 1 : ℝ) / (a + b + 1 : ℝ)^3 ≥ (3 * Real.sqrt 2 - 4) / 2 := by
      have h7 : (a^3 + b^3 + 1 : ℝ) / (a + b + 1 : ℝ)^3 - (3 * Real.sqrt 2 - 4) / 2 ≥ 0 := by
        have pos1 : (a + b + 1 : ℝ) ^ 3 > 0 := by
          positivity
        have h8 : 2 * (a^3 + b^3 + 1) ≥ (3 * Real.sqrt 2 - 4) * (a + b + 1) ^ 3 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a^2 + b^2 - 1), sq_nonneg (a - b), sq_nonneg (a + b - Real.sqrt 2), sq_nonneg (a * b - 1 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_nonneg (a + b - Real.sqrt 2), sq_nonneg (a - Real.sqrt 2 / 2), sq_nonneg (b - Real.sqrt 2 / 2), pow_two_nonneg (a - b), pow_two_nonneg (a + b - Real.sqrt 2), Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), mul_pos ha hb]
        have h9 : (a^3 + b^3 + 1 : ℝ) / (a + b + 1 : ℝ)^3 - (3 * Real.sqrt 2 - 4) / 2 = (2 * (a^3 + b^3 + 1) - (3 * Real.sqrt 2 - 4) * (a + b + 1) ^ 3) / (2 * (a + b + 1) ^ 3) := by
          field_simp
          <;> ring
        rw [h9] at *
        apply div_nonneg
        linarith [h8]
        positivity
      linarith
    linarith [h6]
  have h8 : m < (1 / 4 : ℝ) := by
    have h_eq : m = (a^3 + b^3 + 1) / (a + b + 1)^3 := by
      field_simp [(show (a + b + 1 : ℝ) ≠ 0 by 
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, h]
      )]
      linarith [h1]
    rw [h_eq]
    have h5 : 0 < (a + b + 1 : ℝ) := by
      nlinarith
    have h7 : (a^3 + b^3 + 1 : ℝ) / (a + b + 1 : ℝ)^3 < (1 / 4 : ℝ) := by
      have pos1 : (a + b + 1 : ℝ) ^ 3 > 0 := by
        positivity
      have h8 : 4 * (a^3 + b^3 + 1) < (a + b + 1 : ℝ) ^ 3 := by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_nonneg (a - b), sq_nonneg (a^2 - b^2), sq_nonneg (a - 1/2), sq_nonneg (b - 1/2), sq_nonneg (a + b -1), mul_pos ha hb, mul_pos (show a * b > 0 by nlinarith) (show a * b > 0 by nlinarith), h, sq_nonneg (a*b -0)]
      have h9 : (a^3 + b^3 + 1 : ℝ) / (a + b + 1 : ℝ) ^ 3 < (1 / 4 : ℝ) := by
        apply (div_lt_iff₀ (by positivity)).mpr
        linarith [h8]
      linarith [h9]
    linarith [h7]
  constructor
  · -- First part: (3 * Real.sqrt 2 - 4) / 2 ≤ m
    linarith [h4]
  · -- Second part: m < 1 / 4
    linarith [h8]