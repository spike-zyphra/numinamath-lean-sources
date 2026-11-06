import Mathlib

theorem algebra_328 {a b c : ℝ} (h₀ : a ^ 4 + 9 = 2 * b * (2 * c + b)) (h₁ : b ^ 4 + 9 = 2 * c * (2 * a + c)) (h₂ : c ^ 4 + 9 = 2 * a * (2 * b + a)) : a - b + c = √3 ∨ a - b + c = -√3 := by

  have ha : (a - b)^2 + (b - c)^2 + (c - a)^2 = 0 := by
    nlinarith [sq_nonneg (a^2 - 3), sq_nonneg (b^2 - 3), sq_nonneg (c^2 - 3), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have ha' : (a - b)^2 = 0 := by nlinarith
  have hb' : (b - c)^2 = 0 := by nlinarith
  have hc' : (c - a)^2 = 0 := by nlinarith
  
  have ha'' : a = b := by nlinarith
  have hb'' : b = c := by nlinarith
  
  have ha''' : a^2 = 3 := by
    nlinarith [sq_nonneg (a^2 - 3), sq_nonneg (b^2 - 3), sq_nonneg (c^2 - 3), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have ha4 : a = Real.sqrt 3 ∨ a = -Real.sqrt 3 := by
    have h8 : a^2 = 3 := by nlinarith
    have h9 : a^2 - 3 = 0 := by linarith
    have h10 : (a - Real.sqrt 3) * (a + Real.sqrt 3) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h10) with h11 h12
    · left
      nlinarith
    · right
      nlinarith
  
  cases' ha4 with ha5 ha6
  · -- a = sqrt 3
    have hb5 : b = Real.sqrt 3 := by linarith [ha'', ha5]
    have hc5 : c = Real.sqrt 3 := by linarith [hb'', hb5]
    left
    nlinarith [ha5, hb5, hc5]
  · -- a = -sqrt 3
    have hb6 : b = -Real.sqrt 3 := by linarith [ha'', ha6]
    have hc6 : c = -Real.sqrt 3 := by linarith [hb'', hb6]
    right
    nlinarith [ha6, hb6, hc6]