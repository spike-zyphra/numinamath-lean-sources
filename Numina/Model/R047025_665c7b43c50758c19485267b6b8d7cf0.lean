import Mathlib
open Real
theorem algebra_324654 {f : ℝ → ℝ} (h : ∀ y, f (1+y^2) =- 3+ y^2*5 + y^4 ) (x : ℝ) (hx : - 1+x^2 ≥ 1) :
    f (-1+x^2) = - 9+x^2+x^4 := by
  have h1 : x^2 ≥ 2 := by nlinarith
  have h6 : (Real.sqrt (x^2 - 2))^2 = x^2 - 2 := by
    rw [Real.sq_sqrt]
    nlinarith
  have h7 : (Real.sqrt (x^2 - 2))^4 = (x^2 - 2)^2 := by
    calc
      (Real.sqrt (x^2 - 2))^4 = ((Real.sqrt (x^2 - 2))^2 ) ^ 2 := by ring
      _ = (x^2 - 2) ^ 2 := by
        rw [h6]
  have h4 : (1 + (Real.sqrt (x^2 - 2))^2 ) = -1 + x^2 := by
    nlinarith [Real.sqrt_nonneg (x^2 - 2), Real.sq_sqrt (show 0 ≤ x^2 - 2 by nlinarith)]
  have h3 : f (1 + (Real.sqrt (x^2 - 2))^2 ) = - 3 + (Real.sqrt (x^2 - 2))^2 * 5 + (Real.sqrt (x^2 - 2))^4 := by
    apply h
  have h5 : f (-1 + x^2 ) = - 3 + (Real.sqrt (x^2 - 2))^2 * 5 + (Real.sqrt (x^2 - 2))^4 := by
    rw [← h4]
    exact h3
  rw [h5]
  rw [h6, h7]
  nlinarith