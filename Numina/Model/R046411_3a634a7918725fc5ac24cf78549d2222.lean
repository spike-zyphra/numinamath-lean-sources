import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_289999 {f : ℝ → ℝ} (hf : f = λ x => 2 * sin x - sin (2 * x) + sqrt 3) :
    IsLeast (range f) (-sqrt 3) ↔ False := by
  constructor
  · -- Assume IsLeast (range f) (-sqrt 3)
    intro h 
    have h1 : -sqrt 3 ∈ range f := h.1
    rcases h1 with ⟨x, hx⟩ 
    have eq1 : f x = 2 * sin x - sin (2 * x) + sqrt 3 := by 
      rw [hf]
    have eq3 : 2 * sin x - sin (2 * x) + sqrt 3 = -sqrt 3 := by
      rw [eq1] at hx
      linarith
    -- Simplify using double angle identity
    have eq4 : sin (2 * x) = 2 * sin x * cos x := by 
      rw [sin_two_mul]
    rw [eq4] at eq3
    have h5 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    nlinarith [sq_nonneg (sin x + sqrt 3 / 2), sq_nonneg (cos x - 1 / 2), 
          sq_nonneg (sin x - (-sqrt 3 / 2)), sq_nonneg (cos x - (-1 / 2)), 
          sq_nonneg (sin x), sq_nonneg (cos x - 1), 
          mul_self_nonneg (sin x - (-sqrt 3 / 2)), 
          mul_self_nonneg (cos x - (-1 / 2)), 
          Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
          sq_nonneg (sin x + (sqrt 3 / 2)), sq_nonneg (cos x + 1 / 2), 
          mul_self_nonneg (sin x - (sqrt 3 / 2)), 
          mul_self_nonneg (cos x - (1 / 2)), 
          Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
          sq_nonneg ((1 - cos x) - (3 / 2)), sq_nonneg (sin x + 1)
          ]
  · -- False implies anything
    intro h 
    cases h