import Mathlib

theorem algebra_129322 {p q r : ℝ} (hqr : q = p * (4 - p)) (hrr : r = q * (4 - q))
    (hpp : p = r * (4 - r)) (hqr' : q ≠ r) (hpr : p ≠ r) (hqr'' : q ≠ p) :
    p + q + r = 6 ∨ p + q + r = 7 := by
  have h1 : q = p * (4 - p) := hqr
  have h2 : r = q * (4 - q) := hrr
  have h3 : p = r * (4 - r) := hpp

  have h4 : (p + q + r - 6) * (p + q + r - 7) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show p - q ≠ 0 by
      intro h
      apply hqr''
      linarith
    ), sq_pos_of_ne_zero (show p - r ≠ 0 by
      intro h
      apply hpr
      linarith
    ), sq_pos_of_ne_zero (show r - q ≠ 0 by
      intro h
      apply hqr'
      linarith
    ), sq_nonneg (p - 2), sq_nonneg (q - 2), sq_nonneg (r - 2)]
  
  cases' (mul_eq_zero.mp h4) with h5 h6 
  · -- Case where p + q + r - 6 = 0 
    left
    linarith 
  · -- Case where p + q + r - 7 = 0 
    right
    linarith