import Mathlib

theorem algebra_112086 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ 1 ∧ y ≠ 1) (hlog : Real.logb 2 x = Real.logb y 16) (hxy1 : x * y = 64) :
    (Real.logb 2 (x / y))^2 = 20 := by
  have hy1 : y ≠ 1 := by
    exact hxy.right
  have hx1 : x ≠ 1 := by
    exact hxy.left
  have h1 : Real.logb 2 x = Real.logb y 16 := hlog
  have h2 : Real.logb y 16 = Real.logb 2 16 / Real.logb 2 y := by
    field_simp [Real.logb]
    all_goals linarith
  have h3 : Real.logb 2 16 = 4 := by
    rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
  rw [h2, h3] at h1
  have h4 : Real.logb 2 x * Real.logb 2 y = 4 := by
    field_simp [(show Real.logb 2 y ≠ 0 by
      by_contra h
      have : Real.logb 2 y = 0 := by
        linarith
      have h5 : y = 1 := by
        rw [Real.logb_eq_iff_rpow_eq] at this
        · nlinarith
        all_goals linarith
      contradiction
    )] at h1 ⊢
    nlinarith
  have h5 : Real.logb 2 x + Real.logb 2 y = 6 := by
    have h6 : Real.logb 2 (x * y) = Real.logb 2 x + Real.logb 2 y := by
      rw [Real.logb_mul (by linarith) (by linarith)]
    have h7 : Real.logb 2 (x * y) = 6 := by
      have h8 : x * y = 64 := hxy1
      rw [h8]
      have h9 : Real.logb 2 (64 : ℝ) = 6 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      linarith
    linarith
  have h6 : Real.logb 2 (x / y) = Real.logb 2 x - Real.logb 2 y := by
    field_simp [Real.logb_div, show y ≠ 0 by linarith, show x ≠ 0 by linarith]
    all_goals linarith
  rw [h6]
  have h8 : (Real.logb 2 x - Real.logb 2 y) ^ 2 = 20 := by
    have eq1 : Real.logb 2 x + Real.logb 2 y = 6 := h5
    have eq2 : Real.logb 2 x * Real.logb 2 y = 4 := h4
    nlinarith
  linarith