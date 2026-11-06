import Mathlib

open Real Set

theorem algebra_139063 :
    IsLeast {y : ℝ | ∃ x, y = sqrt (x^2 + 3 * x + 3) + sqrt (x^2 - 3 * x + 3)} (2 * sqrt 3) := by
  constructor
  · -- Show that 2 * sqrt 3 is in the set
    use 0
    have h3 : sqrt (0 ^ 2 + 3 * (0 : ℝ) + 3) + sqrt (0 ^ 2 - 3 * (0 : ℝ) + 3) = 2 * sqrt 3 := by
      have h4 : sqrt (0 ^ 2 + 3 * (0 : ℝ) + 3) = sqrt 3 := by
        norm_num
      have h5 : sqrt (0 ^ 2 - 3 * (0 : ℝ) + 3) = sqrt 3 := by
        norm_num
      rw [h4, h5]
      all_goals ring
    linarith [h3, Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (0 : ℝ), Real.sqrt_nonneg (0 : ℝ)]
  · -- Show that 2 * sqrt 3 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : sqrt (x ^ 2 + 3 * x + 3) + sqrt (x ^ 2 - 3 * x + 3) ≥ 2 * sqrt 3 := by
      have h4 : sqrt (x ^ 2 + 3 * x + 3) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 3 * x + 3)
      have h5 : sqrt (x ^ 2 - 3 * x + 3) ≥ 0 := Real.sqrt_nonneg (x ^ 2 - 3 * x + 3)
      have h6 : (sqrt (x ^ 2 + 3 * x + 3) + sqrt (x ^ 2 - 3 * x + 3)) ^ 2 ≥ (2 * sqrt 3) ^ 2 := by
        have h7 : (sqrt (x ^ 2 + 3 * x + 3) + sqrt (x ^ 2 - 3 * x + 3)) ^ 2 =
          (sqrt (x ^ 2 + 3 * x + 3)) ^ 2 + (sqrt (x ^ 2 - 3 * x + 3)) ^ 2 + 2 * (sqrt (x ^ 2 + 3 * x + 3) * sqrt (x ^ 2 - 3 * x + 3)) := by ring
        have h8 : (sqrt (x ^ 2 + 3 * x + 3)) ^ 2 = x ^ 2 + 3 * x + 3 := by 
          have h11 : x ^ 2 + 3 * x + 3 ≥ 0 := by
            nlinarith [sq_nonneg (x + 3 / 2)]
          rw [Real.sq_sqrt h11]
        have h9 : (sqrt (x ^ 2 - 3 * x + 3)) ^ 2 = x ^ 2 - 3 * x + 3 := by 
          have h12 : x ^ 2 - 3 * x + 3 ≥ 0 := by
            nlinarith [sq_nonneg (x - 3 / 2)]
          rw [Real.sq_sqrt h12]
        have h14 : (2 * sqrt 3) ^ 2 = 12 := by 
          calc
            (2 * sqrt 3) ^ 2 = 4 * (sqrt 3) ^ 2 := by ring
            _ = 4 * 3 := by 
              rw [Real.sq_sqrt]
              all_goals nlinarith
            _ = 12 := by norm_num
        nlinarith [sq_nonneg (sqrt (x ^ 2 + 3 * x + 3) - sqrt (x ^ 2 - 3 * x + 3)), 
          sq_nonneg (x ^ 2 + 3 * x + 3 - (x ^ 2 - 3 * x + 3)), 
          sq_nonneg (x), 
          sq_nonneg (x - 1/2), 
          sq_nonneg (x + 1/2), 
          mul_nonneg (Real.sqrt_nonneg (3 : ℝ)) (Real.sqrt_nonneg (3 : ℝ)), 
          mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 3 * x + 3)) (Real.sqrt_nonneg (x ^ 2 - 3 * x + 3)), 
          Real.sqrt_nonneg (3 : ℝ)
        ]
      nlinarith [Real.sqrt_nonneg (3 : ℝ)]
    linarith [h1, Real.sqrt_nonneg (3 : ℝ)]