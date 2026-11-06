import Mathlib

theorem algebra_304573 {m : ℝ} (hm : m = Real.sqrt 5 + 1) :
    ⌊m + 1 / m⌋ = 3 := by
  have h1 : m = Real.sqrt 5 + 1 := hm
  have h2 : 1 / m = (Real.sqrt 5 - 1) / 4 := by
    rw [h1]
    have h3 : Real.sqrt 5 > 0 := by
      positivity
    field_simp [(show Real.sqrt 5 + 1 ≠ 0 by linarith [h3])]
    <;> nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h3 : m + 1 / m = (5 * Real.sqrt 5 + 3) / 4 := by
    rw [h2, h1]
    linarith
  rw [h3]
  have h4 : 2 < Real.sqrt 5 := by
    rw [Real.lt_sqrt] <;> norm_num
  have h5 : Real.sqrt 5 < 3 := by
    rw [Real.sqrt_lt] <;> norm_num
  have h6 : 3 ≤ (5 * Real.sqrt 5 + 3) / 4 := by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h7 : (5 * Real.sqrt 5 + 3) / 4 < 4 := by
    nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 2.6)]
  have h8 : ⌊(5 * Real.sqrt 5 + 3) / 4⌋ = 3 := by
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try linarith [h6, h7]
  exact h8