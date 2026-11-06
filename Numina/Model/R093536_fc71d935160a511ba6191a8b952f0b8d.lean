import Mathlib

theorem algebra_8212 {x : ℝ} (h : Real.sqrt (36 + x ^ 2) - Real.sqrt (12 + x ^ 2) = 2) :
    Real.sqrt (36 + x ^ 2) + Real.sqrt (12 + x ^ 2) = 12 := by
  have h_eq : (Real.sqrt (36 + x ^ 2) + Real.sqrt (12 + x ^ 2)) * (Real.sqrt (36 + x ^ 2) - Real.sqrt (12 + x ^ 2)) =
    (Real.sqrt (36 + x ^ 2)) ^ 2 - (Real.sqrt (12 + x ^ 2)) ^ 2 := by ring
  rw [h] at h_eq
  have h_a2 : (Real.sqrt (36 + x ^ 2)) ^ 2 = 36 + x ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h_b2 : (Real.sqrt (12 + x ^ 2)) ^ 2 = 12 + x ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h_r : (Real.sqrt (36 + x ^ 2)) ^ 2 - (Real.sqrt (12 + x ^ 2)) ^ 2 = 24 := by
    rw [h_a2, h_b2]
    linarith [sq_nonneg x]

  have h_mul : (Real.sqrt (36 + x ^ 2) + Real.sqrt (12 + x ^ 2)) * 2 = 24 := by
    linarith [h_eq, h_r]

  have h_final : Real.sqrt (36 + x ^ 2) + Real.sqrt (12 + x ^ 2) = 12 := by
    linarith

  exact h_final