import Mathlib

theorem algebra_166883 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h₁ : Real.logb 10 5 = a) (h₂ : Real.logb 10 3 = b) :
    Real.logb 30 8 = 3 * (1 - a) / (1 + b) := by 
  have h3 : Real.logb 30 8 = Real.logb 10 8 / Real.logb 10 30 := by 
    field_simp [Real.logb]
    all_goals linarith
  have h4 : Real.logb 10 8 = 3 * Real.logb 10 2 := by 
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num]
    simp [Real.logb_pow]
    all_goals linarith
  have h5 : Real.logb 10 2 = 1 - a := by
    have h6 : Real.logb 10 5 = a := h₁
    have h7 : Real.logb 10 2 + Real.logb 10 5 = 1 := by 
      have h8 : Real.logb 10 2 + Real.logb 10 5 = Real.logb 10 (2 * 5) := by 
        rw [Real.logb_mul (by norm_num) (by norm_num)]
      have h9 : Real.logb 10 (2 * 5) = 1 := by 
        rw [show (2 * 5 : ℝ) = 10 by norm_num]
        simp [Real.logb_self_eq_one]
      linarith
    linarith [h6, h7]
  have h10 : Real.logb 10 30 = 1 + b := by 
    have h11 : Real.logb 10 30 = Real.logb 10 (3 * 10) := by 
      norm_num
    rw [h11]
    have h12 : Real.logb 10 (3 * 10) = Real.logb 10 3 + Real.logb 10 10 := by 
      rw [Real.logb_mul (by norm_num) (by norm_num)]
    have h13 : Real.logb 10 10 = 1 := Real.logb_self_eq_one (by norm_num)
    rw [h12, h13, h₂]
    all_goals linarith
  rw [h3]
  rw [h4, h5, h10]
  <;> ring_nf <;> simp [show 0 < (30 : ℝ) by norm_num, show 0 < (8 : ℝ) by norm_num] <;> linarith