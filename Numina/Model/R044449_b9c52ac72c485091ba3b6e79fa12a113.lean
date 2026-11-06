import Mathlib

theorem algebra_597366 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + (1 / 3) * y^2 = 25) (h2 : (1 / 3) * y^2 + z^2 = 9)
    (h3 : z^2 + x * z + x^2 = 16) :
    x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
  have eq1 : 3 * x^2 + 3 * x * y + y^2 = 75 := by
    have h := h1
    linarith
  have eq2 : y^2 + 3 * z^2 = 27 := by
    have h := h2
    linarith
  have eq3 : 3 * x^2 + 3 * x * z + 3 * z^2 = 48 := by
    have h := h3
    linarith
  have h12 : 2 * x^2 + x * y + x * z = 32 := by
    nlinarith
  have h15 : (x * y + 2 * y * z + 3 * z * x) ^ 2 = 1728 := by
    nlinarith [sq_nonneg (y - z * Real.sqrt 3), sq_nonneg (x - (Real.sqrt 3) * z), sq_nonneg (x * Real.sqrt 3 - y), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x * Real.sqrt 3 * Real.sqrt 3 - y * (Real.sqrt 3) / Real.sqrt 3)]
  have h16 : (x * y + 2 * y * z + 3 * z * x) = Real.sqrt 1728 := by
    have h18 : (x * y + 2 * y * z + 2 * z * x) > 0 := by positivity
    have h19 : (x * y + 2 * y * z + 3 * z * x) = Real.sqrt ((x * y + 2 * y * z + 3 * z * x) ^ 2) := by
      rw [Real.sqrt_sq (show 0 ≤ (x * y + 2 * y * z + 3 * z * x) by positivity)]
    rw [h19]
    rw [h15]
    all_goals norm_num
  have h16 : Real.sqrt 1728 = 24 * Real.sqrt 3 := by
    have h34 : (24 * Real.sqrt 3) ^ 2 = (1728 : ℝ) := by
      calc 
        (24 * Real.sqrt 3) ^ 2 = (24 : ℝ) ^ 2 * (Real.sqrt 3) ^ 2 := by ring
        _ = (576 : ℝ) * (3 : ℝ) := by
          have ht : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
          rw [ht]
          all_goals norm_num
        _ = (1728 : ℝ) := by norm_num
    have h26 : Real.sqrt 1728 = (24 * Real.sqrt 3) := by
      rw [←h34]
      field_simp
    linarith
  linarith [h16, h16]