import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_74376
  (f : ℝ → ℝ)
  (h₀ : ∀ x y, 0 ≤ x → 0 ≤ y → x ≤ y → f x - 3 * x ≤ f y - 3 * y)
  (h₁ : ∀ x y, 0 ≤ x → 0 ≤ y → x ≤ y → f x - x ^ 3 ≤ f y - y ^ 3) :
  ∀ x y, 0 ≤ x → 0 ≤ y → x ≤ y → f x - x ^ 2 - x ≤ f y - y ^ 2 - y := by
  intro x y hx hy hxy
  have h2 : f x - 3 * x ≤ f y - 3 * y := h₀ x y hx hy hxy
  have h3 : f x - x^3 ≤ f y - y^3 := h₁ x y hx hy hxy
  have h4 : f x ≤ f y + 3 * (x - y) := by linarith
  have h5 : f x ≤ f y + (x - y) * (x^2 + x * y + y^2) := by nlinarith
  by_cases h : x + y > 2
  · -- Case where x + y > 2
    have h6 : x^2 + x * y + y^2 ≥ x + y + 1 := by nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1)]
    nlinarith [h5, h6]
  · -- Case where x + y ≤ 2
    have h6 : 3 * (x - y) ≤ (x - y) * (x + y + 1) := by nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1)]
    nlinarith [h4, h6]