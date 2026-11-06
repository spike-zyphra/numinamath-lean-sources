import Mathlib

theorem algebra_177125 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 19 / x + 98 / y = 1) :
    x + y ≥ 117 + 14 * Real.sqrt 38 := by
  have h1 : 19 * y + 98 * x = x * y := by
    have hx' : x ≠ 0 := by linarith
    have hy' : y ≠ 0 := by linarith
    field_simp [hx', hy'] at h
    nlinarith
  have h2 : (x - 19) * (y - 98) = 1862 := by
    nlinarith [h1]

  have h3 : x + y = (x - 19) + (y - 98) + 117 := by
    linarith

  have h4 : Real.sqrt 38 ^ 2 = 38 := Real.sq_sqrt (by norm_num)
  have h6 : (x - 19) + (y - 98) ≥ 14 * Real.sqrt 38 := by
    nlinarith [sq_nonneg ((x - 19) - 7 * Real.sqrt 38), sq_nonneg ((y - 98) - 7 * Real.sqrt 38),
        Real.sqrt_nonneg 38, Real.sqrt_nonneg 38, Real.sq_sqrt (show (0 : ℝ) ≤ (38 : ℝ) by norm_num),
        sq_nonneg ((x - 19) * (y - 98) - 1862), mul_pos hx hy
    ]

  linarith [h3, h6]