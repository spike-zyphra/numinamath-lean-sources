import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_12086 :
  IsGreatest {y : ℝ | ∃ x, y = (x - x^3) / (1 + x^2)^2} (1/4) ∧
  IsLeast {y : ℝ | ∃ x, y = (x - x^3) / (1 + x^2)^2} (-1/4) := by
  constructor
  · -- Let's prove that 1/4 is the greatest element in the set.
    constructor
    · -- First, show that 1/4 is in the set.
      use Real.sqrt 2 - 1
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have h2 : Real.sqrt 2 > 0 := by positivity
      have eq1 : (Real.sqrt 2 - 1 : ℝ)^2 = 3 - 2 * Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg 2, h1]
      have eq2 : (Real.sqrt 2 - 1 : ℝ)^3 = 5 * Real.sqrt 2 - 7 := by
        calc
          (Real.sqrt 2 - 1 : ℝ)^3 
            = (Real.sqrt 2)^3 - 3 * (Real.sqrt 2)^2 * 1 + 3 * Real.sqrt 2 * (1)^2 - (1 : ℝ)^3 := by ring
          _ = 2 * Real.sqrt 2 - 3 * (2 : ℝ) + 3 * Real.sqrt 2 - (1 : ℝ) := by 
            simp [pow_succ, pow_zero, h1]
          _ = 5 * Real.sqrt 2 - 7 := by 
            linarith
      have eq3 : (Real.sqrt 2 - 1 - (Real.sqrt 2 - 1)^3) = 6 - 4 * Real.sqrt 2 := by 
          nlinarith [Real.sqrt_nonneg 2, h1, eq2]
      have eq4 : (1 + (Real.sqrt 2 - 1)^2 : ℝ) = 4 - 2 * Real.sqrt 2 := by
        nlinarith [h1, eq1]
      have eq5 : ((1 + (Real.sqrt 2 - 1)^2) ^ 2 : ℝ) = (4 - 2 * Real.sqrt 2)^2 := by 
        rw [eq4]
      have eq6 : (Real.sqrt 2 - 1 - (Real.sqrt 2 - 1)^3) / ((1 + (Real.sqrt 2 - 1)^2 )^2) = (1 / 4 : ℝ) := by
        rw [eq3, eq5]
        field_simp [show (4 - 2 * Real.sqrt 2 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_nonneg 2, h1, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
        ]
        <;> nlinarith [Real.sqrt_nonneg 2, h1, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
      linarith [eq6]
    · -- Now, show that 1/4 is the greatest element.
      intro y hy
      rcases hy with ⟨x, hx⟩ 
      have h3 : (x - x^3) / (1 + x^2)^2 ≤ 1/4 := by
        have h4 : (1 + x^2)^2 > 0 := by
          positivity
        apply (div_le_iff₀ h4).mpr 
        nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x^2 - 3), sq_nonneg (x^2 - 2 * Real.sqrt 2), sq_nonneg (x - (Real.sqrt 2 - 1)), sq_nonneg (x + (Real.sqrt 2 - 1)), sq_nonneg (x - (Real.sqrt 2 + 1)), sq_nonneg (x + (Real.sqrt 2 + 1)), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith [h3, hx]
  · -- Let's prove that -1/4 is the least element in the set.
    constructor 
    · -- Show -1/4 is in the set.
      use -(Real.sqrt 2 - 1)
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have h2 : Real.sqrt 2 > 0 := by positivity
      have eq3 : (- (Real.sqrt 2 - 1) : ℝ) - (- (Real.sqrt 2 - 1) )^3  = - (6 - 4 * Real.sqrt 2) := by 
        nlinarith [Real.sqrt_nonneg 2, h1, show (Real.sqrt 2 - 1 : ℝ)^3 = 5 * Real.sqrt 2 - 7 by
          calc 
            (Real.sqrt 2 - 1 : ℝ)^3 
              = (Real.sqrt 2)^3 - 3 * (Real.sqrt 2)^2 * 1 + 3 * Real.sqrt 2 * (1)^2 - (1 : ℝ)^3 := by ring
            _ = 2 * Real.sqrt 2 - 3 * (2 : ℝ) + 3 * Real.sqrt 2 - (1 : ℝ) := by 
              simp [pow_succ, pow_zero, h1]
            _ = 5 * Real.sqrt 2 - 7 := by 
              linarith
        ]
      have eq4 : (1 + ( - (Real.sqrt 2 -1 : ℝ)) ^ 2) = 4 - 2 * Real.sqrt 2 := by
        nlinarith [h1]
      have eq5 : ((1 + ( - (Real.sqrt 2 -1) ) ^ 2) ^ 2 : ℝ) = (4 - 2 * Real.sqrt 2)^2 := by
        rw [eq4]
      have eq6 : (- (Real.sqrt 2 - 1 )  - ( - (Real.sqrt 2 -1 ) ) ^3 ) / ((1 + ( - (Real.sqrt 2 - 1) ) ^ 2) ^ 2) = ( -1 / 4 : ℝ) := by
        rw [eq3, eq5]
        field_simp [show (4 - 2 * Real.sqrt 2 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_nonneg 2, h1, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
        ]
        <;> nlinarith [Real.sqrt_nonneg 2, h1, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
      linarith [eq6]
    · -- Show that -1/4 is the least element.
      intro y hy
      rcases hy with ⟨x, hx⟩ 
      have h3 : -1/4 ≤ (x - x^3) / (1 + x^2)^2 := by
        have h4 : (1 + x^2)^2 > 0 := by
          positivity 
        apply (le_div_iff₀ h4).mpr 
        nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x^2 - 3), sq_nonneg (x^2 - 2 * Real.sqrt 2), sq_nonneg (x - (Real.sqrt 2 - 1)), sq_nonneg (x + (Real.sqrt 2 - 1)), sq_nonneg (x - (Real.sqrt 2 + 1)), sq_nonneg (x + (Real.sqrt 2 + 1)), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith [h3, hx]