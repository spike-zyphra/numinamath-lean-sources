import Mathlib

theorem algebra_201538 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x < y)
    (h₁ : Real.sqrt x + Real.sqrt y = 1) (h₂ : Real.sqrt (x / y) + Real.sqrt (y / x) = 10 / 3) :
    y - x = 1 / 2 := by
  have h3 : Real.sqrt (x / y) = Real.sqrt x / Real.sqrt y := by
    field_simp [Real.sqrt_div]
  have h4 : Real.sqrt (y / x) = Real.sqrt y / Real.sqrt x := by
    field_simp [Real.sqrt_div]
  rw [h3, h4] at h₂
  have h5 : Real.sqrt x > 0 := by
    apply Real.sqrt_pos.mpr
    exact hx
  have h6 : Real.sqrt y > 0 := by
    apply Real.sqrt_pos.mpr
    exact hy
  have h9 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)
  have h10 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith)
  field_simp [show Real.sqrt x > 0 by linarith, show Real.sqrt y > 0 by linarith] at h₂
  have eq1 : (Real.sqrt x + Real.sqrt y) = 1 := by linarith [h₁]
  have eq6 : (Real.sqrt x + Real.sqrt y) ^ 2 = 1 := by
    rw [eq1]
    norm_num
  have eq8 : (Real.sqrt x + Real.sqrt y) ^ 2 = (Real.sqrt x) ^ 2 + (Real.sqrt y) ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) := by
    ring
  rw [h9, h10] at eq8
  have eq9 : (x + y) + 2 * (Real.sqrt x * Real.sqrt y) = 1 := by
    linarith [eq8, eq6]
  have eq10 : Real.sqrt x * Real.sqrt y = (3 / 16) := by
    nlinarith [h₂, eq9]
  have eq4 : x + y = 5 / 8 := by
    nlinarith [h₂, eq9, eq10]
  have eq5 : x * y = 9 / 256 := by
    have eq12 : Real.sqrt x * Real.sqrt y = 3 / 16 := eq10
    have eq13 : (Real.sqrt x * Real.sqrt y) ^ 2 = (9 / 256 : ℝ) := by
      rw [eq12]
      norm_num
    have eq14 : (Real.sqrt x * Real.sqrt y) ^ 2 = (Real.sqrt x) ^ 2 * (Real.sqrt y) ^ 2 := by
      ring
    rw [h9, h10] at eq14
    nlinarith
  have hquad : (x - 1 / 16) * (x - 3 / 8) = 0 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_pos_of_pos hx, sq_pos_of_pos hy, 
      sq_nonneg (y - 9 / 16), sq_nonneg (x - 1 / 16), 
      eq4, eq5
    ]
  cases' (mul_eq_zero.1 hquad) with h7 h8
  · -- Case x = 1 / 16
    have hx1 : x = 1 / 16 := by
      linarith
    have hy1 : y = 9 / 16 := by
      nlinarith [eq4, hx1]
    nlinarith [hx1, hy1]
  · -- Case x = 3 / 8
    have hx2 : x = 3 / 8 := by
      linarith
    have hy2 : y = 1 / 4 := by
      nlinarith [eq4, hx2]
    nlinarith [show x ≥ y from by nlinarith, show x < y from hxy]