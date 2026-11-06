import Mathlib

open Real Set
open scoped Real

theorem algebra_10935 {α β : ℝ} (h : 2 * sin α ^ 2 + sin β ^ 2 - 2 * sin α = 0) :
  1 ≤ cos α ^ 2 + cos β ^ 2 ∧ cos α ^ 2 + cos β ^ 2 ≤ 2 := by
    have h1 : cos α ^ 2 + cos β ^ 2 = 2 - (sin α ^ 2 + sin β ^ 2) := by
      have hcos : cos α ^ 2 + cos β ^ 2 = (1 - sin α ^ 2) + (1 - sin β ^ 2) := by
        rw [Real.cos_sq', Real.cos_sq']
        <;> ring
      linarith

    have h2 : sin β ^ 2 = 2 * sin α - 2 * sin α ^ 2 := by nlinarith

    have h3 : sin α ^ 2 + sin β ^ 2 = 2 * sin α - sin α ^ 2 := by
      nlinarith [h2]

    rw [h1]

    constructor
    · -- Prove lower bound: 1 ≤ cos α ^ 2 + cos β ^ 2
      nlinarith [sq_nonneg (sin α - 1), sq_nonneg (sin β - 1), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]

    · -- Prove upper bound: cos α ^ 2 + cos β ^ 2 ≤ 2
      nlinarith [sq_nonneg (sin α - 1), sq_nonneg (sin β - 1), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β]