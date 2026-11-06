import Mathlib

open Real Set
open scoped Real

theorem algebra_11044 {x : ℝ} :
  (cos x ^ 4 + sin x ^ 4 + sin x ^ 2 * cos x ^ 2) / (sin x ^ 6 + cos x ^ 6 + 2 * sin x ^ 2 * cos x ^ 2) = 1 := by

  have h1 : cos x ^ 2 + sin x ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq x

  have eq1 : cos x ^ 4 + sin x ^ 4 + sin x ^ 2 * cos x ^ 2 = 1 - (sin x ^ 2 * cos x ^ 2) := by
    have h2 : cos x ^ 4 + sin x ^ 4 = (cos x ^ 2 + sin x ^ 2) ^ 2 - 2 * (sin x ^ 2 * cos x ^ 2) := by
      ring
    rw [h2]
    have h3 : cos x ^ 2 + sin x ^ 2 = 1 := h1
    rw [h3]
    all_goals linarith

  have eq3 : sin x ^ 6 + cos x ^ 6 + 2 * sin x ^ 2 * cos x ^ 2 = 1 - (sin x ^ 2 * cos x ^ 2) := by
    have eq2 : sin x ^ 6 + cos x ^ 6 = (cos x ^ 2 + sin x ^ 2) ^ 3 - 3 * (sin x ^ 2 * cos x ^ 2) * (cos x ^ 2 + sin x ^ 2) := by
      ring
    rw [eq2]
    have h3 : cos x ^ 2 + sin x ^ 2 = 1 := h1
    rw [h3]
    all_goals linarith

  have h_eq : cos x ^ 4 + sin x ^ 4 + sin x ^ 2 * cos x ^ 2 = sin x ^ 6 + cos x ^ 6 + 2 * sin x ^ 2 * cos x ^ 2 := by
    linarith [eq1, eq3]

  have h5 : sin x ^ 6 + cos x ^ 6 + 2 * sin x ^ 2 * cos x ^ 2 ≠ 0 := by
    have h7 : sin x ^ 6 + cos x ^ 6 + 2 * sin x ^ 2 * cos x ^ 2 = 1 - (sin x ^ 2 * cos x ^ 2) := eq3
    rw [h7]
    have h8 : sin x ^ 2 * cos x ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg (sin x), sq_nonneg (cos x), sq_nonneg (sin x * cos x)]
    nlinarith [h8]

  rw [show cos x ^ 4 + sin x ^ 4 + sin x ^ 2 * cos x ^ 2 = sin x ^ 6 + cos x ^ 6 + 2 * sin x ^ 2 * cos x ^ 2 by linarith [h_eq]]
  field_simp [h5]