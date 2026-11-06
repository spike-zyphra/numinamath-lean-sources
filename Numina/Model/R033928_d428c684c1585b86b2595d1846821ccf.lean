import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_151168 (f : ℝ → ℝ) (hf : f = λ x => (10 * x + 10) / (x ^ 2 + 2 * x + 2)) :
    IsGreatest (image f (Icc (-1) 2)) 5 ∧ IsLeast (image f (Icc (-1) 2)) 0 := by
  constructor
  · -- Show that 5 is the greatest element in the image of f over [-1, 2]
    constructor
    · -- Show that 5 belongs to the image of f over [-1, 2]
      use 0
      constructor
      · -- Show that 0 is in the interval [-1, 2]
        exact ⟨by norm_num, by norm_num⟩
      · -- Show that f(0) = 5
        rw [hf]
        norm_num
    · -- Show that 5 is indeed greatest
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      rw [hf] at hfx
      simp at hfx
      have h1 : -1 ≤ x := by
        have h1 : x ∈ Icc (-1 : ℝ) 2 := by
          simpa using hx
        exact h1.1
      have h2 : x ≤ 2 := by
        have h1 : x ∈ Icc (-1 : ℝ) 2 := by
          simpa using hx
        exact h1.2
      have hx2_pos : 0 < x ^ 2 + 2 * x + 2 := by
        nlinarith [sq_nonneg (x + 1)]
      have h4 : (10 * x + 10) / (x ^ 2 + 2 * x + 2) ≤ 5 := by
        apply (div_le_iff₀ hx2_pos).mpr
        nlinarith [sq_nonneg (x), sq_nonneg (x + 1)]
      linarith
  · -- Show that 0 is the least element in the image of f over [-1, 2]
    constructor
    · -- Show that 0 belongs to the image of f over [-1, 2]
      use -1
      constructor
      · -- Show that -1 is in the interval [-1, 2]
        exact ⟨by norm_num, by norm_num⟩
      · -- Show that f(-1) = 0
        rw [hf]
        norm_num
    · -- Show that 0 is indeed least
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      rw [hf] at hfx
      simp at hfx
      have h1 : -1 ≤ x := by
        have h1 : x ∈ Icc (-1 : ℝ) 2 := by
          simpa using hx
        exact h1.1
      have h2 : x ≤ 2 := by
        have h1 : x ∈ Icc (-1 : ℝ) 2 := by
          simpa using hx
        exact h1.2
      have hx2_pos : 0 < x ^ 2 + 2 * x + 2 := by
        nlinarith [sq_nonneg (x + 1)]
      have h4 : (10 * x + 10) / (x ^ 2 + 2 * x + 2) ≥ 0 := by
        apply div_nonneg
        all_goals nlinarith
      linarith