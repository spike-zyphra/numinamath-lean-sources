import Mathlib

theorem algebra_9573 (x : ℝ) (hx : 0 < x) :
    Real.logb 4 x + Real.logb 4 (x + 2) + Real.logb 4 (x + 6) = 3 ↔ x = 2 := by
  constructor
  · -- Assume the equation holds, prove x = 2.
    intro h_eq
    have h1 : 0 < x + 2 := by linarith
    have h2 : 0 < x + 6 := by linarith

    have h3 : Real.logb 4 x + Real.logb 4 (x + 2) + Real.logb 4 (x + 6) = Real.logb 4 (x * (x + 2) * (x + 6)) := by
      rw [← Real.logb_mul (by positivity) (by positivity), ← Real.logb_mul (by positivity) (by positivity)]

    rw [h3] at h_eq
  
    have h4 : x * (x + 2) * (x + 6) = 64 := by
      have h5 : Real.logb 4 (x * (x + 2) * (x + 6)) = 3 := h_eq
      have h6 : x * (x + 2) * (x + 6) = (4 : ℝ) ^ (3 : ℝ) := by 
        rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by positivity)] at h5
        · linarith
        all_goals linarith
      norm_num at h6 ⊢
      linarith [h6]
    
    have h5 : (x - 2) * (x ^ 2 + 10 * x + 32) = 0 := by
      nlinarith [sq_nonneg (x + 4)]
    
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- Case x - 2 = 0, so x = 2.
      linarith
    · -- Case x^2 + 10 x + 32 = 0.
      have h8 : x ^ 2 + 10 * x + 32 = 0 := by
        linarith
      nlinarith [sq_nonneg (x + 5)]
  · -- Assume x = 2, prove the equation.
    intro h_eq
    rw [h_eq] 
    have h4 : Real.logb 4 (2 : ℝ) + Real.logb 4 (4 : ℝ) + Real.logb 4 (8 : ℝ) = 3 := by
      have h1 : Real.logb 4 (2 : ℝ) + Real.logb 4 (4 : ℝ) + Real.logb 4 (8 : ℝ) = Real.logb 4 (2 * 4 * 8) := by
        rw [← Real.logb_mul (by norm_num) (by norm_num), ← Real.logb_mul (by norm_num) (by norm_num)]
      rw [h1]
      have h2 : Real.logb 4 (2 * 4 * 8) = 3 := by
        rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)] 
        · norm_num
        all_goals norm_num
      linarith [h2]
    norm_num at h4 ⊢
    linarith [h4]