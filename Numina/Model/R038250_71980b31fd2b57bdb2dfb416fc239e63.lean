import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_148981 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, f x y = 5 * (x ^ 2 + y ^ 2) / 6)
  (h₁ : ∀ x y, x ≥ 0 ∧ y ≥ 0)
  (h₂ : ∀ x y, x ^ 2 + y ^ 2 ≤ 1) :
  ∫ x in (0)..(Real.sqrt 2 / 2), ∫ y in (0)..(Real.sqrt (2 - x ^ 2) / 2),
    ∫ z in (0)..(Real.sqrt (36 * (x ^ 2 + y ^ 2) - z ^ 2)), f x y * z = 2 * π := by 
  have h3 := h₂ 1 1
  norm_num at h3