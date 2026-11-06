import Mathlib

theorem inequalities_599376
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a + b + c = 1) :
    a * Real.sqrt b + b * Real.sqrt c + c * Real.sqrt a ≤ 1 / Real.sqrt 3 := by 
  have h1 : 0 < a + b + c := by linarith
  have h2 : Real.sqrt b ≤ (Real.sqrt 3 / 2) * b + Real.sqrt 3 / 6 := by
    nlinarith [sq_nonneg (Real.sqrt b - Real.sqrt 3 / 3), Real.sq_sqrt (show 0 ≤ b by linarith), 
      Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (b - 1 / 3), 
      Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), 
      mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
  have h3 : Real.sqrt c ≤ (Real.sqrt 3 / 2) * c + Real.sqrt 3 / 6 := by
    nlinarith [sq_nonneg (Real.sqrt c - Real.sqrt 3 / 3), Real.sq_sqrt (show 0 ≤ c by linarith), 
      Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (c - 1 / 3), 
      Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), 
      mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
  have h4 : Real.sqrt a ≤ (Real.sqrt 3 / 2) * a + Real.sqrt 3 / 6 := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt 3 / 3), Real.sq_sqrt (show 0 ≤ a by linarith), 
      Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (a - 1 / 3), 
      Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), 
      mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
  have h5 : a * Real.sqrt b ≤ a * ((Real.sqrt 3 / 2) * b + Real.sqrt 3 / 6) := by
    apply mul_le_mul_of_nonneg_left
    linarith [h2]
    all_goals
      linarith
  have h6 : b * Real.sqrt c ≤ b * ((Real.sqrt 3 / 2) * c + Real.sqrt 3 / 6) := by
    apply mul_le_mul_of_nonneg_left
    linarith [h3]
    all_goals
      linarith
  have h7 : c * Real.sqrt a ≤ c * ((Real.sqrt 3 / 2) * a + Real.sqrt 3 / 6) := by
    apply mul_le_mul_of_nonneg_left
    linarith [h4]
    all_goals
      linarith
  have h8 : a * Real.sqrt b + b * Real.sqrt c + c * Real.sqrt a ≤ a * ((Real.sqrt 3 / 2) * b + Real.sqrt 3 / 6) + b * ((Real.sqrt 3 / 2) * c + Real.sqrt 3 / 6) + c * ((Real.sqrt 3 / 2) * a + Real.sqrt 3 / 6) := by
    linarith [h5, h6, h7]
  have h9 : a * ((Real.sqrt 3 / 2) * b + Real.sqrt 3 / 6) + b * ((Real.sqrt 3 / 2) * c + Real.sqrt 3 / 6) + c * ((Real.sqrt 3 / 2) * a + Real.sqrt 3 / 6) = Real.sqrt 3 / 2 * (a * b + b * c + c * a) + Real.sqrt 3 / 6 * (a + b + c) := by
    ring
  have h10 : a * Real.sqrt b + b * Real.sqrt c + c * Real.sqrt a ≤ Real.sqrt 3 / 2 * (a * b + b * c + c * a) + Real.sqrt 3 / 6 * (a + b + c) := by
    linarith [h8, h9]
  have h11 : a * b + b * c + c * a ≤ 1 / 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
      h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h12 : Real.sqrt 3 / 2 * (a * b + b * c + c * a) + Real.sqrt 3 / 6 * (a + b + c) ≤ Real.sqrt 3 / 3 := by
    have h13 : a + b + c = 1 := h
    rw [show a + b + c = 1 by linarith] 
    nlinarith [h11, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h13 : a * Real.sqrt b + b * Real.sqrt c + c * Real.sqrt a ≤ Real.sqrt 3 / 3 := by
    linarith [h10, h12]
  have h14 : Real.sqrt 3 > 0 := by
    positivity
  have h15 : Real.sqrt 3 / 3 = 1 / Real.sqrt 3 := by
    field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
  linarith [h13, h15]