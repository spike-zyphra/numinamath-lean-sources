import Mathlib

theorem Other_5869 (a : Fin 4 → ℝ) (ha : ∀ i, 0 < a i) :
    4 ≤ (a 0 + a 2) / (a 0 + a 1) + (a 1 + a 3) / (a 1 + a 2) +
        (a 2 + a 0) / (a 2 + a 3) + (a 3 + a 1) / (a 3 + a 0) := by

  have h1 : 0 < a 0 := ha 0
  have h2 : 0 < a 1 := ha 1
  have h3 : 0 < a 2 := ha 2
  have h4 : 0 < a 3 := ha 3
  have h5 : 0 < a 0 + a 1 := by
    linarith [h1, h2]

  have h6 : 0 < a 1 + a 2 := by
    linarith [h2, h3]

  have h7 : 0 < a 2 + a 3 := by
    linarith [h3, h4]

  have h8 : 0 < a 3 + a 0 := by
    linarith [h4, h1]
  have h9 : (a 0 + a 2) / (a 0 + a 1) + (a 1 + a 3) / (a 1 + a 2) + (a 2 + a 0) / (a 2 + a 3) + (a 3 + a 1) / (a 3 + a 0) - 4 ≥ 0 := by
    have hp1 : 0 < (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 3) * (a 3 + a 0) := by positivity
    have h10 : (a 0 + a 2) / (a 0 + a 1) + (a 1 + a 3) / (a 1 + a 2) + (a 2 + a 0) / (a 2 + a 3) + (a 3 + a 1) / (a 3 + a 0) - 4 =
        ((a 0 + a 2) * (a 1 + a 2) * (a 2 + a 3) * (a 3 + a 0) +
          (a 1 + a 3) * (a 0 + a 1) * (a 2 + a 3) * (a 3 + a 0) +
          (a 2 + a 0) * (a 0 + a 1) * (a 1 + a 2) * (a 3 + a 0) +
          (a 3 + a 1) * (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 3) - 4 * (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 3) * (a 3 + a 0)) / ((a 0 + a 1) * (a 1 + a 2) * (a 2 + a 3) * (a 3 + a 0)) := by
      field_simp
      ring
    rw [h10] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a 0 - a 1), sq_nonneg (a 0 - a 2), sq_nonneg (a 0 - a 3), sq_nonneg (a 1 - a 2), sq_nonneg (a 1 - a 3), sq_nonneg (a 2 - a 3),
      sq_nonneg ((a 0 + a 1) - (a 2 + a 3)), sq_nonneg ((a 1 + a 2) - (a 3 + a 0)),
      mul_pos h1 h2, mul_pos h1 h3, mul_pos h1 h4, mul_pos h2 h3, mul_pos h2 h4, mul_pos h3 h4]
    positivity
  linarith [h9]