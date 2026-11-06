import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_310989 (f : ℝ → ℝ)
  (h₁ : ∀ x, |f x + (cos x)^2| ≤ 3 / 4)
  (h₂ : ∀ x, |f x - (sin x)^2| ≤ 1 / 4) :
  ∀ x, f x = (sin x)^2 - 1 / 4 := by
  intro x
  have h1_neg : - 3 / 4 ≤ f x + (cos x)^2 := by
    linarith [abs_le.mp (h₁ x)]
  have h1_pos : f x + (cos x)^2 ≤ (3 : ℝ) / 4 := by
    linarith [abs_le.mp (h₁ x)]
  have h2_neg : - 1 / 4 ≤ f x - (sin x)^2 := by
    linarith [abs_le.mp (h₂ x)]
  have h2_pos : f x - (sin x)^2 ≤ (1 : ℝ) / 4 := by
    linarith [abs_le.mp (h₂ x)]
  have h3 : (sin x ^ 2 + cos x ^ 2) = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have h3' : cos x ^ 2 = 1 - (sin x)^2 := by
    linarith [h3]
  have h4 : f x ≥ (sin x) ^ 2 - 1 / 4 := by
    nlinarith [abs_le.mp (h₁ x), abs_le.mp (h₂ x), h3']
  have h5 : f x ≤ (sin x) ^ 2 - 1 / 4 := by
    nlinarith [abs_le.mp (h₁ x), abs_le.mp (h₂ x), h3']
  linarith [h4, h5]