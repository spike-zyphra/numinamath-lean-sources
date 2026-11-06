import Mathlib

theorem algebra_168593 (a : ℝ) (h : 25 - a^2 ≥ 0 ∧ 9 - a^2 ≥ 0) :
    Real.sqrt (25 - a^2) - Real.sqrt (9 - a^2) = 3 →
    Real.sqrt (25 - a^2) + Real.sqrt (9 - a^2) = 16 / 3 := by
  intro h_eq
  have h1 : Real.sqrt (25 - a^2) ≥ 0 := Real.sqrt_nonneg (25 - a^2)
  have h2 : Real.sqrt (9 - a^2) ≥ 0 := Real.sqrt_nonneg (9 - a^2)
  have h3 : (Real.sqrt (25 - a^2)) ^ 2 = 25 - a^2 := Real.sq_sqrt (by linarith [h.1])
  have h4 : (Real.sqrt (9 - a^2)) ^ 2 = 9 - a^2 := Real.sq_sqrt (by linarith [h.2])
  have h5 : (Real.sqrt (25 - a^2)) ^ 2 - (Real.sqrt (9 - a^2)) ^ 2 = 16 := by 
    linarith [h3, h4, h.1, h.2]
  have h6 : (Real.sqrt (25 - a^2) - Real.sqrt (9 - a^2)) * (Real.sqrt (25 - a^2) + Real.sqrt (9 - a^2)) = 16 := by
    have h7 : (Real.sqrt (25 - a^2) - Real.sqrt (9 - a^2)) * (Real.sqrt (25 - a^2) + Real.sqrt (9 - a^2)) = (Real.sqrt (25 - a^2)) ^ 2 - (Real.sqrt (9 - a^2)) ^ 2 := by
      ring
    rw [h7]
    linarith [h5]
  have h_eq' : Real.sqrt (25 - a^2) - Real.sqrt (9 - a^2) = 3 := by linarith [h_eq]
  have h7 : 3 * (Real.sqrt (25 - a^2) + Real.sqrt (9 - a^2)) = 16 := by
    rw [h_eq'] at h6
    linarith [h6]
  have h8 : Real.sqrt (25 - a^2) + Real.sqrt (9 - a^2) = 16 / 3 := by
    linarith [h7]
  exact h8