import Mathlib

theorem algebra_136547 {x : ℝ} (hx : x = 2^2013) :
    x - Real.sqrt (x^2 + 1) + 1 / (Real.sqrt (x^2 + 1) + x) = 0 := by
  have h1 : 0 < Real.sqrt (x^2 + 1) + x := by
    have h5 : x > 0 := by
      rw [hx]
      positivity
    have h6 : Real.sqrt (x^2 + 1) > 0 := by
      apply Real.sqrt_pos.2
      have h7 : x^2 + 1 > 0 := by
        have h8 : x^2 ≥ 0 := sq_nonneg x
        nlinarith
      linarith
    linarith [Real.sqrt_nonneg (x^2 + 1), h6, h5]
  have h_eq2 : x - Real.sqrt (x^2 + 1) = -1 / (Real.sqrt (x^2 + 1) + x) := by
    have h3 : Real.sqrt (x^2 + 1) ^ 2 = x^2 + 1 := Real.sq_sqrt (by nlinarith [sq_nonneg x])
    have h4 : (Real.sqrt (x^2 + 1) + x) ≠ 0 := by
      linarith [show 0 < Real.sqrt (x^2 + 1) + x from h1]
    field_simp [h4]
    nlinarith [Real.sqrt_nonneg (x^2 + 1), h3]
  rw [h_eq2]
  have h4 : (-1 / (Real.sqrt (x^2 + 1) + x) ) + (1 / (Real.sqrt (x^2 + 1) + x) ) = 0 := by
    have h6 : Real.sqrt (x^2 + 1) + x ≠ 0 := by
      linarith [show 0 < Real.sqrt (x^2 + 1) + x from h1]
    field_simp [h6]
    <;> nlinarith
  linarith [h4]