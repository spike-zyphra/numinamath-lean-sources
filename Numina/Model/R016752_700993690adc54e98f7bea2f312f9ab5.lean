import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_270675 {f : ℝ → ℝ} (hf : f = λ x => (x^2 + x + 2) / (x + 2)) :
    IsLeast (image f (Icc (-1) 1)) 1 ∧ IsGreatest (image f (Icc (-1) 1)) 2 := by
  constructor
  · -- Show that 1 is the least in the image
    constructor
    · -- Show that 1 is in the image
      rw [hf]
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc]
      use 0
      norm_num
    · -- Show that no value smaller than 1 is in the image
      intro y hy
      rw [hf] at hy
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc] at hy
      rcases hy with ⟨x, ⟨hx1, hx2⟩, hfx⟩
      have h1 : x ≥ -1 := by linarith
      have h2 : x ≤ 1 := by linarith
      have h3 : x + 2 > 0 := by
        linarith
      have h4 : (x ^ 2 + x + 2) / (x + 2) ≥ 1 := by
        have h5 : x + 2 > 0 := h3
        apply (le_div_iff₀ h3).mpr
        nlinarith [sq_nonneg x]
      linarith [hfx, h4]
  · -- Show that 2 is the greatest in the image
    constructor
    · -- Show that 2 is in the image
      rw [hf]
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc]
      use -1
      norm_num
    · -- Show that no value greater than 2 is in the image
      intro y hy
      rw [hf] at hy
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc] at hy
      rcases hy with ⟨x, ⟨hx1, hx2⟩, hfx⟩
      have h1 : x ≥ -1 := by linarith
      have h2 : x ≤ 1 := by linarith
      have h3 : x + 2 > 0 := by
        linarith
      have h4 : (x ^ 2 + x + 2) / (x + 2) ≤ 2 := by
        have h5 : x + 2 > 0 := h3
        apply (div_le_iff₀ h5).mpr
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 1)]
      linarith [hfx, h4]