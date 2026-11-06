import Mathlib

open Real Set
open scoped Real

theorem algebra_312961 (x : ℝ) :
  (cos x ^ 4 + sin x ^ 4 + sin x ^ 2 * cos x ^ 2) /
  (sin x ^ 6 + cos x ^ 6 + 2 * sin x ^ 2 * cos x ^ 2) = 1 := by
  have h1 : cos x ^ 4 + sin x ^ 4 + sin x ^ 2 * cos x ^ 2 = 1 - sin x ^ 2 * cos x ^ 2 := by
    have h2 : cos x ^ 2 + sin x ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq x
    have h3 : cos x ^ 4 + sin x ^ 4 = (cos x ^ 2 + sin x ^ 2) ^ 2 - 2 * (sin x ^ 2 * cos x ^ 2) := by
      ring
    rw [h3, h2]
    all_goals
      linarith
  have h2 : sin x ^ 6 + cos x ^ 6 + 2 * sin x ^ 2 * cos x ^ 2 = 1 - sin x ^ 2 * cos x ^ 2 := by
    have h3 : sin x ^ 2 + cos x ^ 2 = 1 := by
      have h3 : cos x ^ 2 + sin x ^ 2 = 1 := by
        exact Real.cos_sq_add_sin_sq x
      linarith
    have h4 : sin x ^ 6 + cos x ^ 6 = (sin x ^ 2 + cos x ^ 2) ^ 3 - 3 * (sin x ^ 2 * cos x ^ 2) * (sin x ^ 2 + cos x ^ 2) := by
      ring
    rw [h4, h3]
    all_goals
      linarith
  have hx1 : (cos x ^ 4 + sin x ^ 4 + sin x ^ 2 * cos x ^ 2) = (sin x ^ 6 + cos x ^ 6 + 2 * sin x ^ 2 * cos x ^ 2) := by
    linarith [h1, h2]
  have h3 : sin x ^ 6 + cos x ^ 6 + 2 * sin x ^ 2 * cos x ^ 2 ≠ 0 := by
    have h5 : sin x ^ 6 + cos x ^ 6 + 2 * sin x ^ 2 * cos x ^ 2 > 0 := by
      have eq1 : sin x ^ 6 + cos x ^ 6 + 2 * sin x ^ 2 * cos x ^ 2 = 1 - sin x ^ 2 * cos x ^ 2 := by
        linarith [h2]
      have eq5 : sin x ^ 2 * cos x ^ 2 ≥ 0 := by
        nlinarith [sq_nonneg (sin x * cos x)]
      have eq6 : 1 - sin x ^ 2 * cos x ^ 2 > 0 := by
        have h6 : sin x ^ 2 * cos x ^ 2 ≤ (1 / 4 : ℝ) := by
          nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x * cos x)]
        linarith
      linarith [eq1, eq6]
    linarith
  rw [hx1]
  field_simp [h3]
  all_goals
    nlinarith