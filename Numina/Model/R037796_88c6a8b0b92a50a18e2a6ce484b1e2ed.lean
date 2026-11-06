import Mathlib

theorem algebra_308851 {a b c : ℝ} (ha : a = Real.sqrt 2 - 1) (hb : b = 2 * Real.sqrt 2 - Real.sqrt 6)
    (hc : c = Real.sqrt 6 - 2) : b < a ∧ a < c := by
  have h1 : 0 < (Real.sqrt 2 : ℝ) := by
    positivity
  have h2 : 0 < (Real.sqrt 6 : ℝ) := by
    positivity 
  have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h4 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h5 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    have h11 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have h12 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h13 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h14 : 0 ≤ (Real.sqrt 6 : ℝ) := by positivity
    have h15 : 0 ≤ (Real.sqrt 2 * Real.sqrt 3 : ℝ) := by positivity
    have h144 : (Real.sqrt 2 * Real.sqrt 3) ^ 2 = 6 := by
      calc
        (Real.sqrt 2 * Real.sqrt 3) ^ 2 = Real.sqrt 2 ^ 2 * Real.sqrt 3 ^ 2 := by ring 
        _ = 2 * 3 := by rw [h12, h13]
        _ = 6 := by norm_num 
    have h24 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, 
          sq_nonneg (Real.sqrt 6 - Real.sqrt 2 * Real.sqrt 3), 
          h14, h15]
    exact h24
  have h6 : 2 * Real.sqrt 2 - Real.sqrt 6 < Real.sqrt 2 - 1 := by 
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, 
        sq_nonneg (Real.sqrt 2 - 1), sq_nonneg (2 * Real.sqrt 2 - Real.sqrt 6), 
        sq_nonneg (Real.sqrt 6 - 1), sq_nonneg (Real.sqrt 6 - (Real.sqrt 2 * 2)), 
        Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (2 : ℝ) by norm_num), 
        Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (6 : ℝ) by norm_num), 
        Real.sqrt_nonneg 3, h3, h4, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), 
        Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, 
        sq_nonneg (Real.sqrt 2 - Real.sqrt 3), 
        mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), h5]
  have h7 : Real.sqrt 2 - 1 < Real.sqrt 6 - 2 := by 
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, 
        sq_nonneg (Real.sqrt 2 - 1), sq_nonneg (Real.sqrt 6 - 2), 
        sq_nonneg (Real.sqrt 6 - 1), sq_nonneg (Real.sqrt 6 - (Real.sqrt 2 * 2)), 
        Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (2 : ℝ) by norm_num), 
        Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (6 : ℝ) by norm_num), 
        Real.sqrt_nonneg 3, h3, h4, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), 
        Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, 
        sq_nonneg (Real.sqrt 2 - Real.sqrt 3), 
        mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), h5]
  constructor
  · -- Show b < a 
    rw [hb, ha]
    linarith [h6]
  · -- Show a < c 
    rw [ha, hc]
    linarith [h7]