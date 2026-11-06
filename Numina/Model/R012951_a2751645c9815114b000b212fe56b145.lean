import Mathlib

theorem inequalities_159502 (x y : ℝ) :
    ((x * y - y^2) / (x^2 + 4 * x + 5))^3 ≤ ((x^2 - x * y) / (x^2 + 4 * x + 5))^3 := by
  have h1 : x^2 + 4 * x + 5 > 0 := by
    nlinarith [sq_nonneg (x + 2)]

  have h2 : ((x^2 - x * y) / (x^2 + 4 * x + 5)) ^ 3 - ((x * y - y^2) / (x^2 + 4 * x + 5)) ^ 3 ≥ 0 := by
    have h3 : ((x^2 - x * y) / (x^2 + 4 * x + 5)) - ((x * y - y^2) / (x^2 + 4 * x + 5)) ≥ 0 := by 
      have h4 : x^2 + 4 * x + 5 > 0 := h1
      have h5 : (x^2 - x * y : ℝ) - (x * y - y^2) ≥ 0 := by
        nlinarith [sq_nonneg (x - y)]
      have h6 : ((x^2 - x * y) / (x^2 + 4 * x + 5)) - ((x * y - y^2) / (x^2 + 4 * x + 5)) = ( (x^2 - x * y) - (x * y - y^2) ) / (x^2 + 4 * x + 5) := by 
        ring_nf
      rw [h6]
      apply div_nonneg
      linarith
      linarith
    have h7 : ((x^2 - x * y) / (x^2 + 4 * x + 5)) ^ 2 + ((x * y - y^2) / (x^2 + 4 * x + 5) ) * ((x^2 - x * y) / (x^2 + 4 * x + 5) ) + ((x * y - y^2) / (x^2 + 4 * x + 5) )^2 ≥ 0 := by
      nlinarith [sq_nonneg ((x^2 - x * y) / (x^2 + 4 * x + 5)), sq_nonneg ((x * y - y^2) / (x^2 + 4 * x + 5)), sq_nonneg ((x^2 - x * y) / (x^2 + 4 * x + 5) + ((x * y - y^2) / (x^2 + 4 * x + 5))), sq_nonneg ((x^2 - x * y) / (x^2 + 4 * x + 5) - ((x * y - y^2) / (x^2 + 4 * x + 5)) ) ]
    have h8 : ((x^2 - x * y) / (x^2 + 4 * x + 5)) ^ 3 - ((x * y - y^2) / (x^2 + 4 * x + 5)) ^ 3 = ( ((x^2 - x * y) / (x^2 + 4 * x + 5)) - ((x * y - y^2) / (x^2 + 4 * x + 5)) ) * ( ((x^2 - x * y) / (x^2 + 4 * x + 5)) ^ 2 + ((x * y - y^2) / (x^2 + 4 * x + 5) ) * ((x^2 - x * y) / (x^2 + 4 * x + 5) ) + ((x * y - y^2) / (x^2 + 4 * x + 5) )^2 ) := by 
      ring_nf
    rw [h8]
    apply mul_nonneg
    · linarith
    · linarith
  
  linarith