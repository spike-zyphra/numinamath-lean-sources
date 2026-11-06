import Mathlib

theorem algebra_13455 {x : ℝ} (hx : x > 0) :
    Real.logb 6 (x^2 + 11) + Real.logb 6 18 - 2 * Real.logb 6 x = 3 ↔ x = 1 := by
  constructor
  · -- Assuming the equation holds, we need to show x = 1
    intro h_eq
    have h1 : Real.logb 6 (x^2 + 11) + Real.logb 6 18 = Real.logb 6 ((x^2 + 11) * 18) := by
      rw [← Real.logb_mul (by positivity) (by positivity)]
    have h2 : 2 * Real.logb 6 x = Real.logb 6 (x ^ 2) := by 
      simp [Real.logb_pow]
    have h3 : Real.logb 6 (x^2 + 11) + Real.logb 6 18 - 2 * Real.logb 6 x = Real.logb 6 ((x^2 + 11) * 18) - Real.logb 6 (x ^ 2) := by
      rw [h1, h2]
    rw [h3] at h_eq
    have h4 : Real.logb 6 ((x^2 + 11) * 18) - Real.logb 6 (x ^ 2) = Real.logb 6 ( ((x^2 + 11) * 18) / (x ^ 2) ) := by
      field_simp [Real.logb_div]
      all_goals positivity
    rw [h4] at h_eq
    -- Now converting to exponential form: $\log_{6}(A) = 3$ means $A = 6^3 = 216$.
    have h5 : ((x^2 + 11) * 18) / (x ^ 2) = (6 : ℝ) ^ 3 := by
      have h6 : Real.logb 6 (( (x^2 + 11) * 18 ) / (x ^ 2) ) = (3 : ℝ) := h_eq
      rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by
        positivity
      )] at h6
      · linarith
      all_goals nlinarith
    have h8 : (6 : ℝ) ^ 3 = 216 := by norm_num
    rw [h8] at h5
    have h9 : ((x^2 + 11) * 18) / (x ^ 2) = (216 : ℝ) := h5
    -- Solving the equation: $\frac{(x^2 + 11) \cdot 18}{x^2} = 216$
    have h10 : (x ^ 2 + 11) * 18 = (216 : ℝ) * (x ^ 2) := by
      have h11 : x^2 > 0 := by positivity
      field_simp at h9
      nlinarith [h9]
    -- Solving: $x^2 = 1$
    have h12 : x^2 = 1 := by
      nlinarith
    -- Therefore x = 1, given x > 0
    have h13 : x = 1 := by
      nlinarith
    exact h13
  · -- Assume x = 1, proving the equation
    intro h_eq
    rw [h_eq]
    have h14 : Real.logb 6 (1^2 + 11) + Real.logb 6 18 - 2 * Real.logb 6 (1 : ℝ) = 3 := by
      have h1 : Real.logb 6 (1 ^ 2 + 11) = Real.logb 6 12 := by
        norm_num
      have h3 : Real.logb 6 (1 : ℝ) = (0 : ℝ) := Real.logb_one
      rw [h1, h3]
      have h4 : Real.logb 6 (12 : ℝ) + Real.logb 6 18 = Real.logb 6 (12 * 18) := by 
        rw [← Real.logb_mul (by norm_num) (by norm_num)]
      have h5 : Real.logb 6 (12 * 18) = (3 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)]
        norm_num
      linarith [h4, h5]
    linarith