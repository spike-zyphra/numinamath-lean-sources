import Mathlib

open Real

theorem algebra_21651 :
    IsGreatest {v : ℝ | ∃(w x y z : ℝ), 0 < w ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧ v = (w * x + x * y + y * z) / (w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2)} ((1 + sqrt 5) / 4) := by
  constructor
  · -- Show that (1 + sqrt 5) / 4 is in the set
    use 1, (1 + Real.sqrt 5) / 2, (1 + Real.sqrt 5) / 2, 1
    constructor
    · norm_num
    constructor
    · -- Show that (1 + Real.sqrt 5) / 2 > 0
      have h1 : 0 < (1 + Real.sqrt 5) / 2 := by
        have h2 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)
        linarith
      linarith
    constructor
    · -- Show that (1 + Real.sqrt 5) / 2 > 0
      have h1 : 0 < (1 + Real.sqrt 5) / 2 := by
        have h2 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)
        linarith
      linarith
    constructor
    · norm_num
    · -- Show that (1 + sqrt 5) / 4 = (w * x + x * y + y * z) / (w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2)
      have h3 : 0 < (5 : ℝ) := by norm_num
      have h4 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      field_simp [show (5 + Real.sqrt 5) ≠ 0 by positivity]
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  · -- Show that (1 + sqrt 5) / 4 is the greatest element in the set
    intro v hv
    rcases hv with ⟨w, x, y, z, hw, hx, hy, hz, heq⟩
    have h1 : 0 < w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 := by
      nlinarith [sq_pos_of_pos hw, sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
    have h2 : (w * x + x * y + y * z) / (w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) ≤ (1 + Real.sqrt 5) / 4 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (w - z), sq_nonneg (x - y), sq_nonneg (x - (1 + Real.sqrt 5) / 2 * w), sq_nonneg (y - (1 + Real.sqrt 5) / 2 * z), sq_nonneg (w - z), sq_nonneg (x - w), sq_nonneg (y - z), Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (x^2 - y^2), sq_nonneg (w^2 - z^2), mul_pos hw hx, mul_pos hx hy, mul_pos hy hz, mul_pos hw hz]
    have h3 : v = (w * x + x * y + y * z) / (w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) := by linarith [heq]
    linarith [h3, h2]