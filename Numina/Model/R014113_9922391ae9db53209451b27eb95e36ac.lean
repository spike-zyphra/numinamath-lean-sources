import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_156159 (f : ℝ → ℝ) (hf : f = λ x => sqrt (100 - x^2)) :
    IsGreatest (image f (Icc (-6) 8)) 10 ∧ IsLeast (image f (Icc (-6) 8)) 6 := by
  constructor
  · -- Show that 10 is greatest element in `f '' Icc (-6) 8`
    constructor
    · -- Show that 10 ∈ `f '' Icc (-6) 8`
      use 0
      constructor
      · -- Show that 0 ∈ `Icc (-6) 8`
        exact ⟨by norm_num, by norm_num⟩
      · -- Show that f(0) = 10
        rw [hf]
        simp [Real.sqrt_eq_iff_sq_eq]
        <;> norm_num
        <;> try { rfl } <;> try { norm_num }
    · -- Show that ∀ y ∈ `f '' Icc (-6) 8`, y ≤ 10
      intro y hy
      rw [hf] at *
      simp only [mem_image, mem_setOf_eq, mem_Icc] at hy ⊢
      rcases hy with ⟨x, hx, rfl⟩
      have h1 : x ≥ -6 := hx.1
      have h2 : x ≤ 8 := hx.2
      have h3 : 100 - x^2 ≤ 100 := by nlinarith
      have h4 : sqrt (100 - x^2) ≤ sqrt (100 : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
      have h5 : sqrt (100 : ℝ) = 10 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h4, h5, Real.sqrt_nonneg (100 - x^2)]
  · -- Show that 6 is least element in `f '' Icc (-6) 8`
    constructor
    · -- Show that 6 ∈ `f '' Icc (-6) 8`
      use 8
      constructor
      · -- Show that 8 ∈ `Icc (-6) 8`
        exact ⟨by norm_num, by norm_num⟩
      · -- Show that f(8) = 6
        rw [hf]
        have h8 : sqrt (100 - (8 : ℝ) ^ 2) = (6 : ℝ) := by
          rw [show 100 - (8 : ℝ) ^ 2 = (36 : ℝ) by norm_num]
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        simp [h8]
        <;> try { rfl } <;> try { norm_num }
    · -- Show that ∀ y ∈ `f '' Icc (-6) 8`, 6 ≤ y
      intro y hy
      rw [hf] at *
      simp only [mem_image, mem_setOf_eq, mem_Icc] at hy ⊢
      rcases hy with ⟨x, hx, rfl⟩
      have h1 : x ≥ -6 := hx.1
      have h2 : x ≤ 8 := hx.2
      have h3 : x^2 ≤ 64 := by nlinarith
      have h4 : 100 - x^2 ≥ (36 : ℝ) := by nlinarith
      have h5 : sqrt (100 - x^2) ≥ sqrt (36 : ℝ) := Real.sqrt_le_sqrt (by nlinarith)
      have h6 : sqrt (36 : ℝ) = (6 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h5, h6, Real.sqrt_nonneg (100 - x^2)]