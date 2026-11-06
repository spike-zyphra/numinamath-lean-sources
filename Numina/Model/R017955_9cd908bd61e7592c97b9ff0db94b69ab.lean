import Mathlib

theorem inequalities_310134 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1) :
    abs (a - b) ≤ Real.sqrt 2 / 2 ∨ abs (b - c) ≤ Real.sqrt 2 / 2 ∨ abs (c - a) ≤ Real.sqrt 2 / 2 := by
  by_contra h1
  push_neg at h1
  have h2 : abs (a - b) > Real.sqrt 2 / 2 := by linarith
  have h3 : abs (b - c) > Real.sqrt 2 / 2 := by linarith
  have h4 : abs (c - a) > Real.sqrt 2 / 2 := by linarith

  have h5 : (a - b) ^ 2 > 1 / 2 := by
    by_contra h5
    push_neg at h5
    have h6 : abs (a - b) ≤ Real.sqrt 2 / 2 := by
      cases' abs_cases (a - b) with h7 h7
      · -- Case where |a-b|=a-b
        nlinarith [h5, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
      · -- Case where |a-b|=-(a-b)
        nlinarith [h5, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
    linarith [h6, h2]

  have h6 : (b - c) ^ 2 > 1 / 2 := by
    by_contra h6
    push_neg at h6
    have h7 : abs (b - c) ≤ Real.sqrt 2 / 2 := by
      cases' abs_cases (b - c) with h7 h7
      · -- Case where |b-c|=b-c
        nlinarith [h6, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
      · -- Case where |b-c|=-(b-c)
        nlinarith [h6, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
    linarith [h7, h3]

  have h7 : (c - a) ^ 2 > 1 / 2 := by
    by_contra h7
    push_neg at h7
    have h8 : abs (c - a) ≤ Real.sqrt 2 / 2 := by
      cases' abs_cases (c - a) with h8 h8
      · -- Case where |c-a|=c-a
        nlinarith [h7, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
      · -- Case where |c-a|=-(c-a)
        nlinarith [h7, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
    linarith [h8, h4]

  have h8 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 > 3 / 2 := by
    linarith [h5, h6, h7]

  have h9 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 2 * (a^2 + b^2 + c^2) - 2 * (a * b + b * c + c * a) := by
    ring

  rw [h9, h] at h8
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (-a + b + c)]