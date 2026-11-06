import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_309494
  (f1 f2 : ℝ → ℝ)
  (h₁ : ∀ x, f1 x = x ^ 2 - 2 * x + 5)
  (h₂ : ∀ x, f2 x = Real.sqrt (|x|)) :
  (∀ x₁ x₂ : ℝ, x₁ ∈ Set.Icc (-1) 1 → x₂ ∈ Set.Icc (-1) 1 → |f1 x₁ - f1 x₂| ≤ 4 * |x₁ - x₂|) ∧
  ¬(∀ x₁ x₂ : ℝ, x₁ ∈ Set.Icc (-1) 1 → x₂ ∈ Set.Icc (-1) 1 → |f2 x₁ - f2 x₂| ≤ 4 * |x₁ - x₂|) := by 
  constructor
  · -- First part: Show that f₁ ∈ M.
    intro x₁ x₂ hx₁ hx₂
    have h1₁ : -1 ≤ x₁ := by
      have h : x₁ ∈ Set.Icc (-1) 1 := hx₁
      exact h.1
    have h1₂ : x₁ ≤ 1 := by
      have h : x₁ ∈ Set.Icc (-1) 1 := hx₁
      exact h.2
    have h2₁ : -1 ≤ x₂ := by
      have h : x₂ ∈ Set.Icc (-1) 1 := hx₂
      exact h.1
    have h2₂ : x₂ ≤ 1 := by
      have h : x₂ ∈ Set.Icc (-1) 1 := hx₂
      exact h.2
    have eq1 : f1 x₁ - f1 x₂ = (x₁ - x₂) * (x₁ + x₂ - 2) := by
      rw [h₁, h₁]
      ring_nf
    have eq2 : |f1 x₁ - f1 x₂| = |x₁ - x₂| * |x₁ + x₂ - 2| := by 
      rw [show f1 x₁ - f1 x₂ = (x₁ - x₂) * (x₁ + x₂ - 2) by linarith [eq1]]
      rw [abs_mul]
    have h3 : |x₁ + x₂ - 2| ≤ 4 := by
      apply abs_le.mpr
      constructor
      · -- Show that -4 ≤ x₁ + x₂ - 2
        linarith 
      · -- Show that x₁ + x₂ - 2 ≤ 4
        linarith 
    calc 
      |f1 x₁ - f1 x₂| = |x₁ - x₂| * |x₁ + x₂ - 2| := by rw [eq2]
      _ ≤ |x₁ - x₂| * 4 := by 
        apply mul_le_mul_of_nonneg_left 
        linarith [abs_nonneg (x₁ + x₂ - 2), h3] 
        linarith [abs_nonneg (x₁ - x₂)]
      _ = 4 * |x₁ - x₂| := by ring 
  · -- Second part: Show that f₂ ∉ M.
    push_neg
    use 0, 0.01
    constructor
    · -- Show that 0 ∈ Set.Icc (-1) 1
      norm_num [Set.mem_Icc]
    constructor
    · -- Show that 0.01 ∈ Set.Icc (-1) 1
      norm_num [Set.mem_Icc]
    · -- Show that |f2 (0) - f2 (0.01)| > 4 * |(0 : ℝ) - (0.01 : ℝ)|
      have eq1 : |f2 (0 : ℝ) - f2 (0.01 : ℝ)| = 0.1 := by
        rw [h₂, h₂]
        have h3 : |(0 : ℝ)| = 0 := by simp 
        have h4 : |(0.01 : ℝ)| = 0.01 := by 
          norm_num [abs_of_nonneg]
        simp only [h3, h4]
        have h5 : Real.sqrt (0 : ℝ) = 0 := Real.sqrt_zero
        have h6 : Real.sqrt (0.01 : ℝ) = 0.1 := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        rw [h5, h6]
        norm_num [abs_of_nonpos]
      have eq2 : (4 : ℝ) * |(0 : ℝ) - (0.01 : ℝ)| = 0.04 := by 
        norm_num [abs_of_nonpos]
      rw [eq1, eq2]
      all_goals norm_num