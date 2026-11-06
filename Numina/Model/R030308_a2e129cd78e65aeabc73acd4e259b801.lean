import Mathlib

theorem algebra_146500 (A : ℝ) (hA : A = 50 + 19 * Real.sqrt 7) :
    A^2 - A * ⌊A⌋ = 27 := by

  have h3 : ⌊A⌋ = 100 := by
    rw [hA]
    have h4 : 100 ≤ (50 + 19 * Real.sqrt 7 : ℝ) := by
      nlinarith [ Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), sq_nonneg (Real.sqrt 7 - 2.6458) ]
    have h5 : (50 + 19 * Real.sqrt 7 : ℝ) < (101 : ℝ) := by
      nlinarith [ Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), sq_nonneg (Real.sqrt 7 - 2.6458) ]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have eq1 : A^2 = 100 * A + 27 := by
    rw [hA]
    have h7 : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), sq_nonneg (Real.sqrt 7 - 2.6458) ]
  rw [h3]
  have eq2 : A ^ 2 - A * (100 : ℝ) = 27 := by 
    linarith [eq1]
  norm_num at eq2 ⊢
  <;> linarith [eq2]