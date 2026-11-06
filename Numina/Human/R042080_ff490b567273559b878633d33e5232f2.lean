import Mathlib
/-Given x≤0, if a-x = 2019, b+|x|=2020,c+√x^2 = 2021. if abc-24, then (a / (b * c) + b / (c * a) + c / (a * b) - 1 / a - 1 / b - 1 / c) ^ ((1 : ℝ) / 3) is ?-/
theorem algebra_212740 (a b c x : ℝ) (hx : x ≤ 0) (ha : a - x = 2019) (hb : b + abs x = 2020)
    (hc : c + Real.sqrt (x^2) = 2021) (habc : a * b * c = 24) :
    ((a / (b * c) + b / (c * a) + c / (a * b) - 1 / a - 1 / b - 1 / c) ^ ((1 : ℝ) / 3)) =
    1 / 2 := by

  -- substitute a b c by x --
  have h_abs_x : abs x = -x := by
    rw [abs_of_nonpos]
    linarith

  have hb_eq : b = 2020 + x := by
    have h1 : abs x = -x := h_abs_x
    linarith [hb, h1]

  have h_sqrt_x : Real.sqrt (x ^ 2) = -x := by
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonpos]
    linarith

  have hc_eq : c = 2021 + x := by
    have h1 : Real.sqrt (x ^ 2) = -x := h_sqrt_x
    linarith [hc, h1]

  have ha_eq : a = 2019 + x := by linarith

  have h1 : (2019 + x) * (2020 + x) * (2021 + x) = 24 := by
    rw [ha_eq, hb_eq, hc_eq] at habc
    nlinarith
 -- solve for x --
  have hx_eq : x = -2017 := by
    nlinarith [sq_nonneg (x + 2017), sq_nonneg (x + 2018), sq_nonneg (x + 2019),
      sq_nonneg (x + 2020), sq_nonneg (x + 2021), sq_nonneg (x + 2019 - 2),
      sq_nonneg (x + 2020 - 3), sq_nonneg (x + 2021 - 4)]
 --solve for a b c --
  have ha2 : a = 2 := by
    rw [ha_eq]
    linarith [hx_eq]

  have hb2 : b = 3 := by
    rw [hb_eq]
    linarith [hx_eq]

  have hc2 : c = 4 := by
    rw [hc_eq]
    linarith [hx_eq]
--plug a b c into the expression --
  have h : a / (b * c) + b / (c * a) + c / (a * b) - 1 / a - 1 / b - 1 / c = 1 / 8 := by
    rw [ha2, hb2, hc2]
    norm_num

  rw [h]
  have h1 : (1 / 8 : ℝ) ^ ((1 : ℝ) / 3) = 1 / 2 := by
    have h2 : (1 / 8 : ℝ) = (1 / 2) ^ (3 : ℝ) := by norm_num
    rw [h2]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num

  rw [h1]