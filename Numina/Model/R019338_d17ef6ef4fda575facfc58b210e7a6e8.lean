import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_325466
  (f g : ℝ → ℝ)
  (h₀ : ∀ x ∈ Set.Icc 0 1, f x ∈ Set.Icc 0 1)
  (h₁ : ∀ y ∈ Set.Icc 0 1, g y ∈ Set.Icc 0 1) :
  ∃ x y : ℝ,
    0 ≤ x ∧ x ≤ 1 ∧
    0 ≤ y ∧ y ≤ 1 ∧
    |x * y - f x - g y| ≥ 1 / 4 := by

  by_contra h
  push_neg at h

  have h2 : |(0 : ℝ) * (0 : ℝ) - f 0 - g 0| < 1 / 4 := by
    apply h 0 0
    all_goals norm_num
  have h3 : |(0 : ℝ) * (1 : ℝ) - f 0 - g 1| < 1 / 4 := by
    apply h 0 1
    all_goals norm_num
  have h4 : |(1 : ℝ) * (0 : ℝ) - f 1 - g 0| < 1 / 4 := by
    apply h 1 0
    all_goals norm_num
  have h5 : |(1 : ℝ) * (1 : ℝ) - f 1 - g 1| < 1 / 4 := by
    apply h 1 1
    all_goals norm_num

  have h2a : -1 / 4 < f 0 + g 0 := by
    cases' abs_lt.mp h2 with h21 h22
    linarith
  have h2b : f 0 + g 0 < 1 / 4 := by
    cases' abs_lt.mp h2 with h21 h22
    linarith

  have h3a : -1 / 4 < f 0 + g 1 := by
    cases' abs_lt.mp h3 with h31 h32
    linarith
  have h3b : f 0 + g 1 < 1 / 4 := by
    cases' abs_lt.mp h3 with h31 h32
    linarith

  have h4a : -1 / 4 < f 1 + g 0 := by
    cases' abs_lt.mp h4 with h41 h42
    linarith
  have h4b : f 1 + g 0 < 1 / 4 := by
    cases' abs_lt.mp h4 with h41 h42
    linarith

  have h5a : -1 / 4 < (1 : ℝ) - f 1 - g 1 := by
    cases' abs_lt.mp h5 with h51 h52
    linarith
  have h5b : (1 : ℝ) - f 1 - g 1 < 1 / 4 := by
    cases' abs_lt.mp h5 with h51 h52
    linarith
  
  have h6 : 0 ≤ f 0 := by
    have h61 : f 0 ∈ Set.Icc (0 : ℝ) 1 := h₀ 0 (by norm_num)
    exact h61.left

  have h7 : f 0 ≤ 1 := by
    have h61 : f 0 ∈ Set.Icc (0 : ℝ) 1 := h₀ 0 (by norm_num)
    exact h61.right

  have h8 : 0 ≤ f 1 := by 
    have h81 : f 1 ∈ Set.Icc (0 : ℝ) 1 := h₀ 1 (by norm_num)
    exact h81.left

  have h9 : f 1 ≤ 1 := by
    have h81 : f 1 ∈ Set.Icc (0 : ℝ) 1 := h₀ 1 (by norm_num)
    exact h81.right

  have h10 : 0 ≤ g 0 := by
    have h101 : g 0 ∈ Set.Icc (0 : ℝ) 1 := h₁ 0 (by norm_num)
    exact h101.left

  have h11 : g 0 ≤ 1 := by
    have h101 : g 0 ∈ Set.Icc (0 : ℝ) 1 := h₁ 0 (by norm_num)
    exact h101.right

  have h12 : 0 ≤ g 1 := by 
    have h121 : g 1 ∈ Set.Icc (0 : ℝ) 1 := h₁ 1 (by norm_num)
    exact h121.left

  have h13 : g 1 ≤ 1 := by 
    have h121 : g 1 ∈ Set.Icc (0 : ℝ) 1 := h₁ 1 (by norm_num)
    exact h121.right

  linarith