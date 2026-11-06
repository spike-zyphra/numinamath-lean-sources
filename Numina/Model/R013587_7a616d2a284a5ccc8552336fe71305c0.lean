import Mathlib

theorem algebra_308377 :
    IsGreatest {(2 * x - y) ^ 2 + (2 * y - z) ^ 2 + (2 * z - x) ^ 2 | (x : ℝ) (y : ℝ) (z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 4)} 28 := by
  constructor
  · -- Show 28 is in the set
    use (-2 * Real.sqrt 2 / Real.sqrt 3)
    use (Real.sqrt 2 / Real.sqrt 3)
    use (Real.sqrt 2 / Real.sqrt 3)
    have h1 : (-2 * Real.sqrt 2 / Real.sqrt 3) ^ 2 + (Real.sqrt 2 / Real.sqrt 3) ^ 2 + (Real.sqrt 2 / Real.sqrt 3) ^ 2 = 4 := by
      have h2 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)
      have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h4 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
    have h6 : (2 * (-2 * Real.sqrt 2 / Real.sqrt 3) - (Real.sqrt 2 / Real.sqrt 3)) ^ 2 + (2 * (Real.sqrt 2 / Real.sqrt 3) - (Real.sqrt 2 / Real.sqrt 3)) ^ 2 + (2 * (Real.sqrt 2 / Real.sqrt 3) - (-2 * Real.sqrt 2 / Real.sqrt 3)) ^ 2 = 28 := by
      have h2 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)
      have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h4 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
    exact ⟨by 
      have h2 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)
      have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h4 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      field_simp at *
      <;> nlinarith, h6⟩
  · -- Show that 28 is the greatest
    intro k hk
    rcases hk with ⟨x, y, z, h, hk⟩
    have h2 : (2 * x - y) ^ 2 + (2 * y - z) ^ 2 + (2 * z - x) ^ 2 ≤ 28 := by
      nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y + z), sq_nonneg (x + y - z), sq_nonneg (-x + y + z), sq_nonneg (x + y + z - 2 * Real.sqrt 6), sq_nonneg (x + y + z + 2 * Real.sqrt 6), Real.sqrt_nonneg 6, Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num)]
    linarith