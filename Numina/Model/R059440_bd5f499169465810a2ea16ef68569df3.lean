import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_112507 {a d : ℝ} (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x^3 + x^2 + x + d)
  (h₁ : ∀ x, |x| ≤ 1 → |f x| ≤ 1) :
  a ∈ Icc (-2) 0 ∧ d ∈ Icc (-2) 0 := by 
  have h1 := h₁ 1 (by norm_num)
  have h2 := h₁ (-1) (by norm_num)
  have h3 := h₁ (0 : ℝ) (by norm_num)
  have hfx1 : f 1 = a * 1^3 + (1 : ℝ)^2 + (1 : ℝ) + d := h₀ 1
  have hfx_1 : f (-1) = a * (-1)^3 + (-1 : ℝ)^2 + (-1 : ℝ) + d := h₀ (-1)
  have hfx0 : f (0 : ℝ) = a * (0 : ℝ)^3 + (0 : ℝ)^2 + (0 : ℝ) + d := h₀ 0
  simp at hfx1 hfx_1 hfx0
  rw [hfx1] at h1
  rw [hfx_1] at h2
  rw [hfx0] at h3
  have h1' : -1 ≤ a + 2 + d := by linarith [abs_le.mp h1]
  have h1'' : a + 2 + d ≤ 1 := by linarith [abs_le.mp h1]
  have h2' : -1 ≤ -a + d := by linarith [abs_le.mp h2]
  have h2'' : -a + d ≤ 1 := by linarith [abs_le.mp h2]
  have h3' : -1 ≤ d := by linarith [abs_le.mp h3]
  have h3'' : d ≤ 1 := by linarith [abs_le.mp h3]
  have ha1 : a ≤ 0 := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3]
  have ha2 : a ≥ -2 := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3]
  have hd1 : d ≤ 0 := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3]
  have hd2 : d ≥ -2 := by
    nlinarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3]
  constructor
  · -- Show a ∈ [-2, 0]
    constructor
    · -- Show a ≥ -2
      linarith
    · -- Show a ≤ 0
      linarith
  · -- Show d ∈ [-2, 0]
    constructor
    · -- Show d ≥ -2
      linarith
    · -- Show d ≤ 0
      linarith