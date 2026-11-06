import Mathlib

theorem inequalities_216243 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x + y) / Real.sqrt (x * y) ≤ x / y + y / x := by 
  have h1 : 0 < x * y := by
    nlinarith
  have h2 : Real.sqrt (x * y) > 0 := by
    apply Real.sqrt_pos.2
    nlinarith
  have h3 : x / y + y / x = (x ^ 2 + y ^ 2) / (x * y) := by
    field_simp
    <;> nlinarith
  have h5 : x / y + y / x ≥ (x + y) / Real.sqrt (x * y) := by
    have h6 : Real.sqrt (x * y) ^ 2 = x * y := by
      rw [Real.sq_sqrt]
      positivity
    have h7 : Real.sqrt (x * y) > 0 := h2
    have h8 : x * y > 0 := h1
    have h9 : x / y + y / x - (x + y) / Real.sqrt (x * y) ≥ 0 := by
      have h13 : Real.sqrt (x * y) > 0 := h2
      have h14 : x / y + y / x - (x + y) / Real.sqrt (x * y) =
          ( (x ^ 2 + y ^ 2) * Real.sqrt (x * y) - (x + y) * (x * y) ) / ( (x * y) * Real.sqrt (x * y) ) := by
        field_simp
        <;> nlinarith [Real.sqrt_nonneg (x * y), Real.sq_sqrt (show (0 : ℝ) ≤ x * y by positivity) ]
      rw [h14]
      have h15 : (x ^ 2 + y ^ 2) * Real.sqrt (x * y) - (x + y) * (x * y) ≥ 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (Real.sqrt (x * y) - x/2 - y/2), sq_nonneg (Real.sqrt (x * y) - (x + y) / 2), 
          Real.sqrt_nonneg (x * y), Real.sq_sqrt (show (0 : ℝ) ≤ x * y by positivity),
          sq_nonneg (x^2 - y^2), sq_nonneg (x * y - Real.sqrt (x * y) ^ 2), 
          sq_nonneg (x * Real.sqrt (x * y) - y * Real.sqrt (x * y) ) ]
      have h16 : (x * y) * Real.sqrt (x * y) > 0 := by
        positivity
      apply div_nonneg
      linarith
      all_goals positivity
    linarith
  linarith [h3, h5]