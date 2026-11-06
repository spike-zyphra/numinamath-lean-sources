import Mathlib

theorem algebra_186885 (x : ℝ) (hx : x^3 + 8 ≥ 0) :
    Real.sqrt (x^3 + 8) + (x^3 + 8) ^ ((1 : ℝ) / 4) = 6 ↔ x = 2 := by
  constructor
  · -- Assume Real.sqrt (x^3 + 8) + (x^3 + 8) ^ ((1 : ℝ) / 4) = 6, prove x = 2
    intro h_eq
    have h1 : Real.sqrt (x ^ 3 + 8) = ((x^3 + 8) ^ ((1 : ℝ) / 4)) ^ 2 := by
      have h2 : ((x^3 + 8) ^ ((1 : ℝ) / 4)) ^ 2 = (x^3 + 8) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith [show 0 ≤ x^3 + 8 from hx]
      have h3 : Real.sqrt (x^3 + 8) = (x^3 + 8) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      rw [h3]
      rw [h2]
    rw [h1] at h_eq
    have h4 : ((x^3 + 8) ^ ((1 : ℝ) / 4)) ^ 2 + ((x^3 + 8) ^ ((1 : ℝ) / 4)) - 6 = 0 := by
      nlinarith [h_eq]
    have ht2 : ((x^3 + 8) ^ ((1 : ℝ) / 4)) = 2 := by
      have ht : ((x^3 + 8) ^ ((1 : ℝ) / 4)) ^ 2 + ((x^3 + 8) ^ ((1 : ℝ) / 4)) - 6 = 0 := h4
      have h5 : ((x^3 + 8) ^ ((1 : ℝ) / 4)) ≥ 0 := by positivity
      nlinarith [sq_nonneg ((x^3 + 8) ^ ((1 : ℝ) / 4) - 2), sq_nonneg ((x^3 + 8) ^ ((1 : ℝ) / 4) + 3)]
    have h6 : (x^3 + 8) = 16 := by
      have ht2' : ((x^3 + 8) ^ ((1 : ℝ) / 4)) = 2 := ht2
      have h7 : ((x^3 + 8) ^ ((1 : ℝ) / 4)) ^ 4 = (2: ℝ) ^ 4 := by rw [ht2']
      have h8 : ((x^3 + 8) ^ ((1 : ℝ) / 4)) ^ 4 = x^3 + 8 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith [show 0 ≤ x^3 + 8 from hx]
      rw [h8] at h7
      norm_num at h7
      linarith [h7]
    have h8 : x^3 = 8 := by nlinarith [h6]
    have h2' : x = 2 := by
      have h9 : x^3 - 8 = 0 := by linarith [h8]
      have h10 : (x - 2) * (x^2 + 2 * x + 4) = 0 := by
        nlinarith [h9]
      cases' (mul_eq_zero.mp h10) with h11 h12
      · -- x - 2 = 0
        linarith [h11]
      · -- x^2 + 2 * x + 4 = 0
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x ^ 2 + 2 * x + 4)]
    exact h2'
  · -- Assume x = 2
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt ((2 : ℝ) ^ 3 + 8) = 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : ((2 : ℝ) ^ 3 + 8) ^ ((1 : ℝ) / 4) = 2 := by
      have h4 : ((2 : ℝ) ^ 3 + 8) ^ ((1 : ℝ) / 4) = (16 : ℝ) ^ (1 / 4 : ℝ) := by norm_num
      rw [h4]
      have h5 : (16 : ℝ) ^ (1 / 4 : ℝ) = (2 : ℝ) := by
        rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      rw [h5]
    rw [h1, h2]
    all_goals norm_num