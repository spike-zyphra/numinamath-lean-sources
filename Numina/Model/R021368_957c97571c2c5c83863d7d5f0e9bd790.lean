import Mathlib

theorem algebra_285877 : ⌊(2 + √3)^3⌋ = 51 := by
  have h1 : (2 + Real.sqrt 3 : ℝ) ^ 3 = 26 + 15 * Real.sqrt 3 := by
    ring_nf
    have h2 : (Real.sqrt 3) ^ 2 = 3 := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    have h3 : (Real.sqrt 3) ^ 3 = 3 * (Real.sqrt 3) := by
      calc
        (Real.sqrt 3) ^ 3 = (Real.sqrt 3) ^ 2 * (Real.sqrt 3) := by ring
        _ = 3 * (Real.sqrt 3) := by rw [h2]
    nlinarith [h2, h3, Real.sqrt_nonneg 3]
  rw [h1]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> 
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg (Real.sqrt 3 - 5 / 3), sq_nonneg (Real.sqrt 3 - 26 / 15)]