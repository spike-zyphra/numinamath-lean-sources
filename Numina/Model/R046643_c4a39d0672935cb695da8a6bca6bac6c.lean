import Mathlib

theorem algebra_327915 {x y : ℝ}
    (hx : x = (Real.sqrt 3 - 1) / (Real.sqrt 3 + 1)) (hy : y = (Real.sqrt 3 + 1) / (Real.sqrt 3 - 1)) :
    x^4 + y^4 = 194 := by
  have hxy : x * y = 1 := by
    rw [hx, hy]
    have h1 : 0 < Real.sqrt 3 := by positivity
    have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    field_simp [(show Real.sqrt 3 + 1 ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    ), (show Real.sqrt 3 - 1 ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    )
    ]
    <;> nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have hxy2 : x + y = 4 := by
    rw [hx, hy]
    have h1 : 0 < Real.sqrt 3 := by positivity
    have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    field_simp [(show Real.sqrt 3 + 1 ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    ), (show Real.sqrt 3 - 1 ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    )
    ]
    <;> nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have hxy2sq : x^2 + y^2 = 14 := by
    have h1 : x + y = 4 := hxy2
    have h2 : x * y = 1 := hxy
    calc
      x^2 + y^2 = (x + y)^2 - 2 * (x * y) := by ring
      _ = 4^2 - 2 * 1 := by rw [h1, h2]
      _ = 16 - 2 := by norm_num
      _ = 14 := by norm_num
  calc
    x^4 + y^4 = (x^2 + y^2)^2 - 2 * (x * y)^2 := by ring
    _ = 14^2 - 2 * (1)^2 := by rw [hxy2sq, hxy]
    _ = 196 - 2 * 1 := by norm_num
    _ = 194 := by norm_num