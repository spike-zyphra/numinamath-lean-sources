import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_209061 :
  IsLeast {z : ℝ | ∃ x y : ℝ, |x| < 1 ∧ |y| < 2 ∧ x * y = 1 ∧ z = 1 / (1 - x ^ 2) + 4 / (4 - y ^ 2)} 4 := by
  constructor
  · -- Show 4 is in the set.
    use Real.sqrt 2 / 2, Real.sqrt 2
    have h1 : Real.sqrt 2 < (2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h2 : Real.sqrt 2 > (0 : ℝ) := by
      apply Real.sqrt_pos.mpr
      linarith
    have hx1 : |Real.sqrt 2 / 2| < 1 := by
      have h3 : Real.sqrt 2 / 2 > 0 := by
        have h4 : Real.sqrt 2 > 0 := h2
        linarith
      rw [abs_of_pos h3]
      have h4 : Real.sqrt 2 < (2 : ℝ) := h1
      linarith
    have hy1 : |Real.sqrt 2| < 2 := by
      have h3 : Real.sqrt 2 > 0 := h2
      rw [abs_of_pos h3]
      linarith [h1]
    have hxy1 : (Real.sqrt 2 / 2 : ℝ) * Real.sqrt 2 = 1 := by
      have h4 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      nlinarith [h4]
    constructor
    · exact hx1
    constructor
    · exact hy1
    constructor
    · exact hxy1
    · -- Show z = 4.
      have h3 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = (1 / 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h4 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      norm_num [h3, h4]
  · -- Show no value less than 4 is in the set
    intro z hz
    rcases hz with ⟨x, y, hx1, hy1, hxy1, hz⟩
    have h5 : x ^ 2 < 1 := by
      nlinarith [abs_lt.mp hx1]
    have h6 : y ^ 2 < 4 := by
      nlinarith [abs_lt.mp hy1]
    have h7 : 1 - x ^ 2 > 0 := by
      nlinarith
    have h8 : 4 - y ^ 2 > 0 := by
      nlinarith
    have h1 : 1 / (1 - x ^ 2) + 4 / (4 - y ^ 2) ≥ 4 := by
      have h5 : x ^ 2 < 1 := by
        nlinarith [abs_lt.mp hx1]
      have h6 : y ^ 2 < 4 := by
        nlinarith [abs_lt.mp hy1]
      have h7 : 1 - x ^ 2 > 0 := by
        nlinarith
      have h8 : 4 - y ^ 2 > 0 := by
        nlinarith
      have h9 : x * y = 1 := hxy1
      have h10 : 1 / (1 - x ^ 2) + 4 / (4 - y ^ 2) - 4 ≥ 0 := by
        have h11 : 0 < (1 - x ^ 2) * (4 - y ^ 2) := by
          nlinarith
        have h14 : (1 / (1 - x ^ 2) + 4 / (4 - y ^ 2) - 4) = ( (4 - y^2) + 4*(1 - x^2) - 4*(1 - x^2)*(4 - y^2) ) / ( (1 - x^2)*(4 - y^2) ) := by
          field_simp [(show (1 - x^2 : ℝ) ≠ 0 by nlinarith), (show (4 - y^2 : ℝ) ≠ 0 by nlinarith)]
          <;> ring
        rw [h14] at *
        apply div_nonneg
        nlinarith [sq_nonneg (x ^ 2 - 1 / 2), sq_nonneg (y ^ 2 - 2), sq_nonneg (x * y - 1), sq_nonneg (x - Real.sqrt (1 / 2)), sq_nonneg (x + Real.sqrt (1 / 2)), Real.sqrt_pos.mpr (show (1 / 2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (1 / 2 : ℝ) ≥ 0 by norm_num), mul_pos (show 0 < 1 - x^2 by nlinarith) (show 0 < 4 - y^2 by nlinarith) ]
        all_goals
          nlinarith
      linarith
    have h2 : z = 1 / (1 - x ^ 2) + 4 / (4 - y ^ 2) := by
      linarith [hz]
    linarith [h1, h2]