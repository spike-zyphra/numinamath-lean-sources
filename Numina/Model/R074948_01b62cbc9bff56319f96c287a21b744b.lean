import Mathlib

theorem algebra_5626 {x y : ℝ} (h : abs (x - 2019) + (y + 2017)^2 = 0) :
    x + y + (x + y)^2 + (x + y)^3 + (x + y)^4 + (x + y)^5 + (x + y)^6 + (x + y)^7 +
    (x + y)^8 + (x + y)^9 + (x + y)^10 + (x + y)^11 + (x + y)^12 + (x + y)^13 +
    (x + y)^14 + (x + y)^15 + (x + y)^16 + (x + y)^17 + (x + y)^18 + (x + y)^19 +
    (x + y)^20 = 2097150 := by 
  have h1 : abs (x - 2019) ≥ 0 := abs_nonneg (x - 2019)
  have h2 : (y + 2017) ^ 2 ≥ 0 := sq_nonneg (y + 2017)
  have h3 : abs (x - 2019) = 0 := by linarith [h, h1, h2]
  have h4 : (y + 2017) ^ 2 = 0 := by linarith [h, h1, h2]
  have hx : x - 2019 = 0 := abs_eq_zero.mp h3
  have hx2 : x = 2019 := by linarith
  have hy : y + 2017 = 0 := by
    rw [sq_eq_zero_iff] at h4
    exact h4
  have hy2 : y = -2017 := by linarith
  rw [hx2, hy2]
  norm_num