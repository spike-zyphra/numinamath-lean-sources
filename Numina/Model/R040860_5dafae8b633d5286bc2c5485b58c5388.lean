import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_298236 : ⌊(tan (π / 3) + 2 * cos (π / 4))^6⌋ = 969 := by
  have htan : tan (π / 3) = Real.sqrt 3 := by
    rw [tan_pi_div_three]
  have hcos : cos (π / 4) = Real.sqrt 2 / 2 := by
    rw [cos_pi_div_four]
  rw [htan, hcos]
  have h1 : (Real.sqrt 3 + 2 * (Real.sqrt 2 / 2)) = Real.sqrt 3 + Real.sqrt 2 := by ring
  rw [h1]
  have h2 : (Real.sqrt 3 + Real.sqrt 2) ^ 6 = 485 + 198 * Real.sqrt 6 := by
    have h5 : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
      have h12 : (6 : ℝ) = 3 * 2 := by norm_num
      rw [h12]
      rw [Real.sqrt_mul (by norm_num)]
    have h10 : (Real.sqrt 3 + Real.sqrt 2) ^ 2 = 5 + 2 * Real.sqrt 6 := by
      calc
        (Real.sqrt 3 + Real.sqrt 2) ^ 2 = (Real.sqrt 3) ^ 2 + (Real.sqrt 2) ^ 2 + 2 * (Real.sqrt 3 * Real.sqrt 2) := by ring
        _ = 3 + 2 + 2 * (Real.sqrt 3 * Real.sqrt 2) := by
          have h1 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
          have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
          rw [h1, h2]
          all_goals norm_num
        _ = 5 + 2 * Real.sqrt 6 := by
          have h3 : (Real.sqrt 3 * Real.sqrt 2 : ℝ) = Real.sqrt 6 := by
            have h5' : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
              have h12 : (6 : ℝ) = 3 * 2 := by norm_num
              rw [h12]
              rw [Real.sqrt_mul (by norm_num)]
            linarith [h5']
          rw [h3]
          all_goals ring
    have h11 : (Real.sqrt 3 + Real.sqrt 2) ^ 4 = 49 + 20 * Real.sqrt 6 := by
      calc
        (Real.sqrt 3 + Real.sqrt 2) ^ 4 = ((Real.sqrt 3 + Real.sqrt 2) ^ 2) ^ 2 := by ring
        _ = (5 + 2 * Real.sqrt 6) ^ 2 := by rw [h10]
        _ = 49 + 20 * Real.sqrt 6 := by
          nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    calc
      (Real.sqrt 3 + Real.sqrt 2) ^ 6 = (Real.sqrt 3 + Real.sqrt 2) ^ 4 * (Real.sqrt 3 + Real.sqrt 2) ^ 2 := by ring
      _ = (49 + 20 * Real.sqrt 6) * (5 + 2 * Real.sqrt 6) := by rw [h11, h10]
      _ = 485 + 198 * Real.sqrt 6 := by
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  rw [h2]
  have h3 : (485 + 198 * Real.sqrt 6) < (970 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num)
    ]
  have h4 : (485 + 198 * Real.sqrt 6) ≥ (969 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num)
    ]
  have h7 : ⌊(485 + 198 * Real.sqrt 6)⌋ = 969 := by
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try linarith [h3, h4]
  exact h7