import Mathlib

open Real
theorem algebra_10836 : IsGreatest {t | ∃ x y z : ℝ, -1/3 ≤ x ∧ -1 ≤ y ∧ -5/3 ≤ z ∧ x + y + z = 1 ∧
t = sqrt (3 * x + 1) + sqrt (3 * y + 3) + sqrt (3 * z + 5)} 6 := by
  constructor
  · -- Show that 6 is in the set.
    use 1, 1 / 3, -1 / 3
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show that x + y + z = 1
      norm_num
    · -- Show that 6 = sqrt (3 * 1 + 1) + sqrt (3 * (1 / 3) + 3) + sqrt (3 * (-1 / 3) + 5)
      have h1 : sqrt (3 * (1 : ℝ) + 1) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : sqrt (3 * (1 / 3 : ℝ) + 3) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h3 : sqrt (3 * (-1 / 3 : ℝ) + 5) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h1, h2, h3]
  · -- Show that 6 is greatest.
    intro t ht
    rcases ht with ⟨x, y, z, h1, h2, h3, h4, heq⟩
    have h5 : sqrt (3 * x + 1) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h6 : sqrt (3 * y + 3) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h7 : sqrt (3 * z + 5) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h8 : (sqrt (3 * x + 1) ) ^ 2 = 3 * x + 1 := by
      have h9 : 3 * x + 1 ≥ 0 := by
        nlinarith
      have h10 : (sqrt (3 * x + 1) ) ^ 2 = (3 * x + 1) := Real.sq_sqrt (h9)
      linarith
    have h9 : (sqrt (3 * y + 3) ) ^ 2 = 3 * y + 3 := by
      have h10 : 3 * y + 3 ≥ 0 := by
        nlinarith
      have h11 : (sqrt (3 * y + 3) ) ^ 2 = (3 * y + 3) := Real.sq_sqrt (h10)
      linarith
    have h10 : (sqrt (3 * z + 5) ) ^ 2 = 3 * z + 5 := by
      have h11 : 3 * z + 5 ≥ 0 := by
        nlinarith
      have h12 : (sqrt (3 * z + 5) ) ^ 2 = (3 * z + 5) := Real.sq_sqrt (h11)
      linarith
    have h11 : (sqrt (3 * x + 1) + sqrt (3 * y + 3) + sqrt (3 * z + 5)) ^ 2 ≤ 36 := by
      nlinarith [ sq_nonneg (sqrt (3 * x + 1) - sqrt (3 * y + 3) ), sq_nonneg (sqrt (3 * x + 1) - sqrt (3 * z + 5) ), sq_nonneg (sqrt (3 * y + 3) - sqrt (3 * z + 5) ), 
          Real.sqrt_nonneg (3 * x + 1), Real.sqrt_nonneg (3 * y + 3), Real.sqrt_nonneg (3 * z + 5), 
          mul_nonneg (Real.sqrt_nonneg (3 * x + 1)) (Real.sqrt_nonneg (3 * y + 3)), 
          mul_nonneg (Real.sqrt_nonneg (3 * x + 1)) (Real.sqrt_nonneg (3 * z + 5) ), 
          mul_nonneg (Real.sqrt_nonneg (3 * y + 3)) (Real.sqrt_nonneg (3 * z + 5) )
        ]
    have h12 : sqrt (3 * x + 1) + sqrt (3 * y + 3) + sqrt (3 * z + 5) ≤ 6 := by
      nlinarith [ h5, h6, h7, h11 ]
    linarith [ heq, h12 ]