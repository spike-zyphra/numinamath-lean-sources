import Mathlib

open Real Set
open scoped Real

theorem algebra_233369 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = cos x ^ 2 + cos (π / 6 + x) ^ 2 - 2 * cos (π / 6) * cos x * cos (π / 6 + x)) :
  ∃ c, ∀ x, f x = c ∧ c = 1 / 4 := by

  use 1 / 4

  intro x

  -- Show the original expression
  have eq1 : f x = 1 / 4 := by

    rw [h₀ x]

    have h1 : cos (π / 6 + x) = cos (π / 6) * cos x - sin (π / 6) * sin x := by
      rw [cos_add]

    have h2 : cos (π / 6) = Real.sqrt 3 / 2 := by
      exact cos_pi_div_six

    have h3 : sin (π / 6) = 1 / 2 := by
      exact sin_pi_div_six

    rw [h1, h2, h3]

    have h4 : cos x ^ 2 + sin x ^ 2 = 1 := by
      exact cos_sq_add_sin_sq x

    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq (π / 6 + x), sq_nonneg (sin (π / 6 + x)), sq_nonneg (cos (π / 6 + x))]

  constructor
  · -- Show that f x = 1 / 4
    linarith [eq1]
  · -- Show that 1 / 4 = 1 / 4
    rfl