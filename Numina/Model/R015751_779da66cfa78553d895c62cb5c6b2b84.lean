import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_271904 (x : Fin 3 → ℝ)
  (hx : ∀ i, 0 < x i)
  (hsum : ∑ i, x i = 1) :
  x 0 * x 1 ^ 2 * x 2 + x 0 * x 1 * x 2 ^ 2 ≤ 27 / 1024 := by
  have h1 : x 0 + x 1 + x 2 = 1 := by 
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hsum ⊢
    linarith
  have h2 : 0 < x 0 := hx 0
  have h3 : 0 < x 1 := hx 1
  have h4 : 0 < x 2 := hx 2

  have h5 : x 0 = 1 - x 1 - x 2 := by
    linarith
  
  rw [h5]

  nlinarith [sq_nonneg (x 1 - x 2), sq_nonneg ((1 - x 1 - x 2) - x 1), sq_nonneg ((1 - x 1 - x 2) - x 2), 
    sq_nonneg (x 1 + x 2 - 3 / 4), sq_nonneg (x 1 - 3 / 8), sq_nonneg (x 2 - 3 / 8), 
    mul_pos h2 h3, mul_pos h3 h4, mul_pos h2 h4, 
    mul_pos (show 0 < x 1 * x 2 by nlinarith) (show 0 < (1 - x 1 - x 2) by nlinarith)]