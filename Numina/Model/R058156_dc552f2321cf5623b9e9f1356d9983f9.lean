import Mathlib

theorem algebra_320476 {x : ℝ} (hx : x = (Real.sqrt 5 + 1) / 2) : (x^3 + x + 1) / x^5 = (Real.sqrt 5 - 1) / 2 := by
  have h1 : Real.sqrt 5 ^ 2 = 5 := by
    exact Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
  rw [hx]
  have h3 : Real.sqrt 5 ^ 4 = 25 := by
    calc
      Real.sqrt 5 ^ 4 = (Real.sqrt 5 ^ 2) ^ 2 := by ring
      _ = 5 ^ 2 := by rw [h1]
      _ = 25 := by norm_num
  have h4 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by
    calc
      Real.sqrt 5 ^ 3 = Real.sqrt 5 ^ 2 * Real.sqrt 5 := by ring
      _ = 5 * Real.sqrt 5 := by rw [h1]
  field_simp [pow_two, pow_three, pow_succ, h1, h3, h4]
  ring_nf
  <;> nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < (5:ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]