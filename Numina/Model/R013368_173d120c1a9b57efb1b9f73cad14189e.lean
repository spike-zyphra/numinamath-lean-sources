import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_125305
  (f : ℝ → ℝ)
  (h₀ : ∀ x ∈ Set.Icc 0 1, f x > 0)
  (h₁ : f 1 = 1)
  (h₂ : ∀ x y : ℝ, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 → x + y ∈ Set.Icc 0 1 → f (x + y) ≥ f x + f y) :
  ∀ x ∈ Set.Icc 0 1, f x ≤ 2 * x := by
  have h3 : f 0 > 0 := h₀ 0 (by norm_num)
  have h4 : f (0 + (0 : ℝ)) ≥ f 0 + f 0 := by
    apply h₂
    all_goals norm_num
  have h5 : f 0 ≥ f 0 + f 0 := by
    simp at h4 ⊢
    linarith
  have h6 : f 0 ≤ 0 := by
    linarith
  linarith