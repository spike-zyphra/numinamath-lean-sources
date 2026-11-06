import Mathlib

open Real

theorem algebra_3298 :
  IsGreatest {y : ℝ | ∃ x, x ∈ Set.Icc 10 46 ∧ y = sqrt (x - 10) + sqrt (110 - x)} 14 := by 
  constructor
  · -- Show that 14 belongs to the set
    use 46
    constructor
    · norm_num [Set.mem_Icc]
    · -- Show that sqrt(46 - 10) + sqrt(110 - 46) = 14
      have h1 : sqrt ((46 : ℝ) - 10) = 6 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : sqrt ((110 : ℝ) - 46) = 8 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2]
      norm_num
  · -- Show that 14 is the greatest element in the set
    intro y hy
    rcases hy with ⟨x, hx, hy⟩
    rw [hy]
    have hx1 : 10 ≤ x := by
      exact hx.1
    have hx2 : x ≤ 46 := by
      exact hx.2
    have h1 : sqrt (x - 10) + sqrt (110 - x) ≤ 14 := by
      nlinarith [sq_nonneg (sqrt (x - 10) - 6), sq_nonneg (sqrt (110 - x) - 8), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x - 10 by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 110 - x by linarith), 
          Real.sqrt_nonneg (x - 10), Real.sqrt_nonneg (110 - x), 
          mul_nonneg (Real.sqrt_nonneg (x - 10)) (Real.sqrt_nonneg (110 - x)), 
          sq_nonneg (sqrt (x - 10) ^ 2 - 36), sq_nonneg (sqrt (110 - x) ^ 2 - 64), 
          mul_nonneg (show (0 : ℝ) ≤ (x - 10) by linarith) 
            (show (0 : ℝ) ≤ (110 - x) by linarith), 
          mul_nonneg (Real.sqrt_nonneg (x - 10)) (Real.sqrt_nonneg (110 - x)), 
          sq_nonneg (sqrt (x - 10) - sqrt (110 - x)), 
          Real.sqrt_nonneg (x - 10), Real.sqrt_nonneg (110 - x), 
          sq_nonneg (x - 46), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x - 10 : ℝ) by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (110 - x : ℝ) by linarith)
      ]
    linarith