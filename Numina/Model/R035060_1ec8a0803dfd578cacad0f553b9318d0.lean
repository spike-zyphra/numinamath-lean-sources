import Mathlib

theorem algebra_2972 :
  IsGreatest {w : ℝ | (∃ x y t z : ℝ, w = x * z ∧ x ^ 2 + y ^ 2 = 25 ∧ t ^ 2 + z ^ 2 = 16 ∧ x * t - y * z = 20)} 10 := by
  constructor
  · -- Show 10 is in the set
    use 5 / 2 * Real.sqrt 2, -5 / 2 * Real.sqrt 2, 2 * Real.sqrt 2, 2 * Real.sqrt 2
    constructor
    · -- Show that w = x * z
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor
    · -- Show that x ^ 2 + y ^ 2 = 25
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor
    · -- Show that t ^ 2 + z ^ 2 = 16
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Show that x * t - y * z = 20
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show that 10 is the greatest element in the set
    intro w hw
    rcases hw with ⟨x, y, t, z, h_eq, h1, h2, h3⟩
    nlinarith [sq_nonneg (x - z), sq_nonneg (t - y), sq_nonneg (x * t - y * z), sq_nonneg (x * z + y * t), sq_nonneg (y - (5 / 4) * z), sq_nonneg (t - z), sq_nonneg (y), sq_nonneg (x - (5 / 4) * t), sq_nonneg (t * z - 8), sq_nonneg (t * z + 8)]