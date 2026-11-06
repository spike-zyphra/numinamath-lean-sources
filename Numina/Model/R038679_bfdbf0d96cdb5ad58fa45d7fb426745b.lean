import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_51255 :
  IsLeast {x | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 3 ∧ x = sqrt (a * (b + 3)) + sqrt (b * (c + 3)) + sqrt (c * (a + 3))} 3 ∧
  IsGreatest {x | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 3 ∧ x = sqrt (a * (b + 3)) + sqrt (b * (c + 3)) + sqrt (c * (a + 3))} 6 := by 
  constructor
  · -- Show 3 is the least element in the set
    constructor
    · -- Show 3 is in the set
      use 0, 0, 3
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Show 3 is achievable
        have h1 : sqrt (0 * (0 + 3)) = 0 := by
          norm_num [sqrt_eq_zero]
        have h2 : sqrt (0 * (3 + 3)) = 0 := by
          norm_num [sqrt_eq_zero]
        have h3 : sqrt (3 * (0 + 3)) = 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        linarith [h1, h2, h3]
    · -- Show no value less than 3 is in the set
      intro x hx
      rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
      have h2 : sqrt (a * (b + 3)) + sqrt (b * (c + 3)) + sqrt (c * (a + 3)) ≥ 3 := by
        nlinarith [sq_nonneg (sqrt (a * (b + 3)) - 0), sq_nonneg (sqrt (b * (c + 3)) - 0), sq_nonneg (sqrt (c * (a + 3)) - 3),
          Real.sqrt_nonneg (a * (b + 3)), Real.sqrt_nonneg (b * (c + 3)), Real.sqrt_nonneg (c * (a + 3)),
          sq_nonneg (a - 0), sq_nonneg (b - 0), sq_nonneg (c - 3),
          Real.sq_sqrt (show 0 ≤ a * (b + 3) by nlinarith), Real.sq_sqrt (show 0 ≤ b * (c + 3) by nlinarith), Real.sq_sqrt (show 0 ≤ c * (a + 3) by nlinarith),
          mul_nonneg (Real.sqrt_nonneg (a * (b + 3))) (Real.sqrt_nonneg (b * (c + 3))), 
          mul_nonneg (Real.sqrt_nonneg (b * (c + 3))) (Real.sqrt_nonneg (c * (a + 3))), 
          mul_nonneg (Real.sqrt_nonneg (c * (a + 3))) (Real.sqrt_nonneg (a * (b + 3))), 
          h1, mul_nonneg ha (show 0 ≤ b + 3 by nlinarith), mul_nonneg hb (show 0 ≤ c + 3 by nlinarith), mul_nonneg hc (show 0 ≤ a + 3 by nlinarith)
        ]
      linarith [h2, hx]
  · -- Show 6 is the greatest element in the set
    constructor
    · -- Show 6 is in the set
      use 1, 1, 1
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Show 6 is achievable
        have h1 : sqrt (1 * (1 + 3)) = 2 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        linarith [h1]
    · -- Show no value greater than 6 is in the set
      intro x hx
      rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
      have h21 : sqrt (a * (b + 3)) + sqrt (b * (c + 3)) + sqrt (c * (a + 3)) ≤ 6 := by
        nlinarith [sq_nonneg (sqrt (a * (b + 3)) - 2), sq_nonneg (sqrt (b * (c + 3)) - 2), sq_nonneg (sqrt (c * (a + 3)) - 2),
          Real.sqrt_nonneg (a * (b + 3)), Real.sqrt_nonneg (b * (c + 3)), Real.sqrt_nonneg (c * (a + 3)),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          Real.sq_sqrt (show 0 ≤ a * (b + 3) by nlinarith), Real.sq_sqrt (show 0 ≤ b * (c + 3) by nlinarith), Real.sq_sqrt (show 0 ≤ c * (a + 3) by nlinarith),
          mul_nonneg (Real.sqrt_nonneg (a * (b + 3))) (Real.sqrt_nonneg (b * (c + 3))), 
          mul_nonneg (Real.sqrt_nonneg (b * (c + 3))) (Real.sqrt_nonneg (c * (a + 3))), 
          mul_nonneg (Real.sqrt_nonneg (c * (a + 3))) (Real.sqrt_nonneg (a * (b + 3))), 
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha
        ]
      linarith [h21, hx]