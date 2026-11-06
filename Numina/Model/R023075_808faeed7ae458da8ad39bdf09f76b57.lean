import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_103381 :
  IsGreatest {y : ℝ | ∃ x, y = sqrt (x^2 - x^4) + sqrt (2 * x^2 - x^4)} (sqrt 2) := by 
  constructor
  · -- Show that sqrt 2 is in the set 
    use Real.sqrt (2 / 3)
    have h1 : Real.sqrt (2 / 3) ^ 2 = 2 / 3 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    have h2 : Real.sqrt (2 / 3) ^ 4 = (2 / 3) ^ 2 := by
      calc
        Real.sqrt (2 / 3) ^ 4 = (Real.sqrt (2 / 3) ^ 2) ^ 2 := by ring
        _ = (2 / 3) ^ 2 := by rw [h1]
    have h3 : Real.sqrt (2 / 3) ^ 2 - Real.sqrt (2 / 3) ^ 4 = (2 / 9 : ℝ) := by
      rw [h1, h2]
      all_goals norm_num
    have h4 : 2 * Real.sqrt (2 / 3) ^ 2 - Real.sqrt (2 / 3) ^ 4 = (8 / 9 : ℝ) := by
      rw [h1, h2]
      all_goals norm_num
    have h5 : Real.sqrt (Real.sqrt (2 / 3) ^ 2 - Real.sqrt (2 / 3) ^ 4) = Real.sqrt (2) / 3 := by
      rw [h3]
      have h6 : Real.sqrt ((2 / 9 : ℝ)) = Real.sqrt 2 / 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num
      rw [h6]
    have h7 : Real.sqrt (2 * Real.sqrt (2 / 3) ^ 2 - Real.sqrt (2 / 3) ^ 4) = 2 * Real.sqrt (2) / 3 := by
      rw [h4]
      have h8 : Real.sqrt ((8 / 9 : ℝ)) = 2 * Real.sqrt 2 / 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num
      rw [h8]
    rw [h5, h7]
    ring
  · -- Show that sqrt 2 is the greatest in the set.
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h41 : sqrt (x ^ 2 - x ^ 4) ≥ 0 := by positivity
    have h42 : sqrt (2 * x ^ 2 - x ^ 4) ≥ 0 := by positivity
    have h4 : (sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 - x ^ 4)) ^ 2 ≤ (2 : ℝ) := by
      by_cases h11 : x ^ 2 - x ^ 4 ≥ 0
      · -- Case 1: `x^2 - x^4` ≥ 0, so can apply Real.sq_sqrt
        by_cases h12 : 2 * x ^ 2 - x ^ 4 ≥ 0
        · -- Both conditions positive. Then expand (f(x))^2.
          have h10a : sqrt (x ^ 2 - x ^ 4) ^ 2 = x ^ 2 - x ^ 4 := by 
            apply Real.sq_sqrt
            linarith 
          have h10b : sqrt (2 * x ^ 2 - x ^ 4) ^ 2 = 2 * x ^ 2 - x ^ 4 := by 
            apply Real.sq_sqrt
            linarith
          nlinarith [sq_nonneg (sqrt (x ^ 2 - x ^ 4) - sqrt (2 * x ^ 2 - x ^ 4)), 
            sq_nonneg (x^2 - (2 * x ^ 2 - x^4)), 
            sq_nonneg (x^2 - 2/3), 
            mul_nonneg (Real.sqrt_nonneg (x^2 - x^4)) (Real.sqrt_nonneg (2 * x^2 - x^4)), 
            sq_nonneg (x^2 - x^2 * 2)
            ]
        · -- Case 1 with second expression not ≥ 0
          have h10a : sqrt (x ^ 2 - x ^ 4) ^ 2 = x ^ 2 - x ^ 4 := by 
            apply Real.sq_sqrt
            linarith 
          have h10b : sqrt (2 * x ^ 2 - x ^ 4) = (0 : ℝ) := by
            rw [Real.sqrt_eq_zero']
            linarith 
          rw [h10b] 
          nlinarith [Real.sqrt_nonneg (x ^ 2 - x ^ 4), Real.sqrt_nonneg (0 : ℝ), sq_nonneg (x ^ 2 -4/9)]
      · -- Case 1 is false. So sqrt(x^2 - x^4) = 0 works.
        by_cases h12 : 2 * x ^ 2 - x ^ 4 ≥ 0
        · -- Case when (x^2 - x^4) <0 also  {sqrt 2 * x ^ 2} is valid.
          have h111 : sqrt (x ^ 2 - x ^ 4) = (0 : ℝ) := by
            rw [Real.sqrt_eq_zero']
            linarith
          rw [h111] 
          have h10b : sqrt (2 * x ^ 2 - x ^ 4) ^ 2 = 2 * x ^ 2 - x ^ 4 := by
            apply Real.sq_sqrt
            linarith
          nlinarith [Real.sqrt_nonneg (x ^ 2 -x ^ 4), Real.sqrt_nonneg (2 * x^2 -x ^ 4), 
            sq_nonneg (x^2 - 4/9)
            ]
        · -- Both expressions negatives inside.
          have h111 : sqrt (x ^ 2 - x ^ 4) = (0 : ℝ) := by
            rw [Real.sqrt_eq_zero']
            linarith
          rw [h111] 
          have h10b : sqrt (2 * x ^ 2 - x ^ 4) = (0 : ℝ) := by 
            rw [Real.sqrt_eq_zero']
            linarith
          rw [h10b] 
          nlinarith
    have h5 : (sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 - x ^ 4)) ≤ Real.sqrt 2 := by 
      have h4' : (sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 - x ^ 4)) ^ 2 ≤ (2 : ℝ) := h4
      have h51 : sqrt ((sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 - x ^ 4)) ^ 2) ≤ sqrt (2 : ℝ) := Real.sqrt_le_sqrt h4'
      have h54 : sqrt ((sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 - x ^ 4)) ^ 2) = sqrt (x ^ 2 - x ^ 4) + sqrt (2 * x ^ 2 - x ^ 4) := by
        apply Real.sqrt_sq 
        positivity 
      linarith [h54, h51]
    linarith [hx, h5]