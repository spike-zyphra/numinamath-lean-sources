import Mathlib

open Real

theorem algebra_163399 (α β : ℝ) :
    sin (α - 2 * β) ^ 2 - cos α ^ 2 - cos (2 * β) ^ 2 =
    -2 * cos α * cos (2 * β) * cos (α - 2 * β) := by

  have h1 : sin (α - 2 * β) = sin α * cos (2 * β) - cos α * sin (2 * β) := by
    rw [sin_sub]

  have h4 : cos (α - 2 * β) = cos α * cos (2 * β) + sin α * sin (2 * β) := by
    rw [cos_sub]

  rw [h1, h4]

  have h2 : sin α ^ 2 + cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α

  have h3 : sin (2 * β) ^ 2 + cos (2 * β) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (2 * β)

  nlinarith [Real.sin_sq_add_cos_sq (α), Real.sin_sq_add_cos_sq (2 * β),
    sq_nonneg (sin α - cos α), sq_nonneg (sin (2 * β) - cos (2 * β)),
    sq_nonneg (sin α * sin (2 * β) - cos α * cos (2 * β))
  ]