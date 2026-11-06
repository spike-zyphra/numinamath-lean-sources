import Mathlib

theorem algebra_2256 {x m : ℝ} (hx : 1 ≤ x) (hm : 0 < m) (h : Real.sqrt (x + 3) - Real.sqrt (x - 1) = m) :
    Real.sqrt (x + 3) + Real.sqrt (x - 1) = 4 / m := by
  have h1 : Real.sqrt (x + 3) ≥ 0 := Real.sqrt_nonneg (x + 3)
  have h2 : Real.sqrt (x - 1) ≥ 0 := Real.sqrt_nonneg (x - 1)
  have h3 : Real.sqrt (x + 3) = m + Real.sqrt (x - 1) := by linarith
  have h4 : Real.sqrt (x + 3) ^ 2 - Real.sqrt (x - 1) ^ 2 = 4 := by
    have h5 : Real.sqrt (x + 3) ^ 2 = x + 3 := by
      apply Real.sq_sqrt
      linarith
    have h6 : Real.sqrt (x - 1) ^ 2 = x - 1 := by
      apply Real.sq_sqrt
      linarith
    linarith
  have h6 : (Real.sqrt (x + 3) + Real.sqrt (x - 1)) * m = 4 := by
    have h7 : (Real.sqrt (x + 3) + Real.sqrt (x - 1)) * (Real.sqrt (x + 3) - Real.sqrt (x - 1)) = 4 := by 
      nlinarith [h4]
    rw [h] at h7
    nlinarith
  have h6' : Real.sqrt (x + 3) + Real.sqrt (x - 1) = 4 / m := by
    field_simp [show m ≠ 0 by linarith]
    nlinarith
  linarith