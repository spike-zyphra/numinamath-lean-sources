import Mathlib

theorem algebra_20726 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (h : Real.logb y x + Real.logb x y = 7) :
    (Real.logb y x) ^ 2 + (Real.logb x y) ^ 2 = 47 := by
  have h1 : Real.logb y x * Real.logb x y = 1 := by
    have h2 : Real.logb y x = Real.log x / Real.log y := by
      field_simp [Real.logb]
    have h3 : Real.logb x y = Real.log y / Real.log x := by
      field_simp [Real.logb]
    rw [h2, h3]

    have h4 : Real.log x ≠ 0 := by
      have hx2 : x > 0 := hx
      have hx3 : x ≠ 1 := hx1
      exact Real.log_ne_zero_of_pos_of_ne_one hx2 hx3
    have h5 : Real.log y ≠ 0 := by
      have hy2 : y > 0 := hy
      have hy3 : y ≠ 1 := hy1
      exact Real.log_ne_zero_of_pos_of_ne_one hy2 hy3

    field_simp [h4, h5]

  have h2 : (Real.logb y x) ^ 2 + (Real.logb x y) ^ 2 = (Real.logb y x + Real.logb x y) ^ 2 - 2 * (Real.logb y x * Real.logb x y) := by
    ring
  rw [h2, h, h1]
  all_goals norm_num