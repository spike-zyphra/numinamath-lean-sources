import Mathlib

theorem algebra_225020 (x y : ℝ) (h₀ : x^2 - 3 * x * y + 2 * y^2 + x - y = 0) (h₁ : x^2 - 2 * x * y + y^2 - 5 * x + 7 * y = 0) :
    x * y - 12 * x + 15 * y = 0 := by

  have h2 : (x - y) * (x - 2 * y + 1) = 0 := by
    linarith [h₀]

  cases' (mul_eq_zero.mp h2) with h3 h4
  
  · -- Case 1: x = y
    have hx_eq_y : x = y := by linarith
    rw [hx_eq_y] at h₁
    have hy : y = 0 := by nlinarith
    rw [hx_eq_y, hy]
    linarith

  · -- Case 2: x = 2y - 1
    have hx_eq_2y_minus_1 : x = 2 * y - 1 := by linarith
    rw [hx_eq_2y_minus_1] at h₁
    have h5 : y^2 - 5 * y + 6 = 0 := by nlinarith
    have hy_eq_2_or_3 : (y - 2) * (y - 3) = 0 := by 
      linarith [h5]

    cases' (mul_eq_zero.mp hy_eq_2_or_3) with hy_eq_2 hy_eq_3
    
    · -- Subcase 1: y = 2
      have hy_eq_2' : y = 2 := by linarith
      have hx_eq_3 : x = 3 := by 
        rw [hx_eq_2y_minus_1, hy_eq_2']
        linarith
      rw [hx_eq_3, hy_eq_2']
      linarith

    · -- Subcase 2: y = 3
      have hy_eq_3' : y = 3 := by linarith
      have hx_eq_5 : x = 5 := by 
        rw [hx_eq_2y_minus_1, hy_eq_3']
        linarith
      rw [hx_eq_5, hy_eq_3']
      linarith