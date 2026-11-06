import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_31975
  (f : ℝ → ℝ)
  (h₀ : ∀ x y, x ∈ Set.Icc 0 1 → y ∈ Set.Icc 0 1 → x ≠ y → f x ≠ f y)
  (h₁ : f 0 + f 1 = 1) :
  ∃ x₁ x₂ : ℝ, x₁ ∈ Set.Icc 0 1 ∧ x₂ ∈ Set.Icc 0 1 ∧ x₁ ≠ x₂ ∧ 2 * f x₁ < f x₂ + 1 / 2 := by
  by_cases h2 : f 0 < 1 / 2
  · -- Case where f 0 < 1 / 2
    use 0, 1
    constructor
    · -- Show 0 in [0, 1]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 1 in [0, 1]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 0 ≠ 1
      norm_num
    · -- Show 2 * f 0 < f 1 + 1 / 2
      have h3 : f 1 = 1 - f 0 := by linarith
      rw [h3]
      linarith
  · -- Case where f 0 ≥ 1 / 2
    have h4 : f 0 ≥ 1 / 2 := by linarith
    use 1, 0
    constructor
    · -- Show 1 in [0, 1]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 0 in [0, 1]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 1 ≠ 0
      norm_num
    · -- Show 2 * f 1 < f 0 + 1 / 2
      have h5 : f 1 = 1 - f 0 := by linarith
      rw [h5]
      by_contra h
      push_neg at h
      have h6 : f 0 ≤ 1 / 2 := by linarith
      have h8 : f 0 = 1 / 2 := by linarith
      have h9 : f 1 = 1 / 2 := by
        linarith [h₁, h8]
      have h10 : f 1 ≠ f 0 := by
        apply h₀ 1 0 (by norm_num) (by norm_num) (by norm_num)
      have h11 : f 1 = f 0 := by
        linarith [h9, h8]
      contradiction