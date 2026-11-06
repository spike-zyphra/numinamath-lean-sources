import Mathlib

theorem algebra_287792 (x : ℝ) :
    (x + 1)^5 + (x + 1)^4 * (x - 1) + (x + 1)^3 * (x - 1)^2 +
    (x + 1)^2 * (x - 1)^3 + (x + 1) * (x - 1)^4 + (x - 1)^5 = 0 ↔ x = 0 := by
  constructor
  · -- Assume the equation holds, prove x = 0
    intro h
    have eq1 : (x + 1)^5 + (x + 1)^4 * (x - 1) + (x + 1)^3 * (x - 1)^2 +
        (x + 1)^2 * (x - 1)^3 + (x + 1) * (x - 1)^4 + (x - 1)^5 = 
        ((x + 1)^6 - (x - 1)^6) / 2 := by
      ring
    have eq2 : ((x + 1)^6 - (x - 1)^6) / 2 = 0 := by
      rw [eq1] at h
      linarith
    have eq3 : (x + 1)^6 - (x - 1)^6 = 0 := by
      linarith [eq2]
    have eq4 : x = 0 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 3), sq_nonneg (x * (x ^ 2)), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg (x * (x + 1)), sq_nonneg (x * (x - 1)), sq_nonneg ((x ^ 2 - 1) * x)]
    exact eq4
  · -- Assume x = 0, prove the equation
    intro h
    rw [h]
    norm_num