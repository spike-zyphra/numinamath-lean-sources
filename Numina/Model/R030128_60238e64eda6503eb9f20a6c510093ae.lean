import Mathlib

open Real Set
open scoped Real

theorem algebra_315680 {x y : ℝ} (hy : 0 ≤ y ∧ y ≤ π/2)
  (h1 : x + sin y = 2008) (h2 : x + 2008 * cos y = 2007) :
  x + y = 2007 + π/2 := by
  have h3 : sin y - 2008 * cos y = 1 := by
    nlinarith
  have h4 : cos y ≥ 0 := by 
    have h5 : 0 ≤ y := hy.1
    have h6 : y ≤ π / 2 := hy.2
    apply cos_nonneg_of_mem_Icc
    constructor
    · linarith [h5, Real.pi_pos]
    · linarith [h6, Real.pi_pos]
  have h5 : sin y ≥ 0 := by 
    have h6 : 0 ≤ y := hy.1
    have h7 : y ≤ π / 2 := hy.2
    apply sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · linarith [Real.pi_pos, h7]
  have h6 : cos y = 0 := by
    have h7 : sin y = 1 + 2008 * cos y := by 
      linarith [h3]
    have h8 : sin y ≤ 1 := by 
      have h5 : sin y ≤ 1 := sin_le_one y
      linarith
    have h9 : cos y ≤ 0 := by
      nlinarith [h7, h8]
    linarith [h4, h9]
  have h7 : sin y = 1 := by
    rw [h6] at h3
    linarith
  have h8 : x = 2007 := by
    linarith [h1, h7]
  have h9 : y = π / 2 := by
    have h10 : cos y = 0 := h6
    have h5 : 0 ≤ y := hy.1
    have h6 : y ≤ π / 2 := hy.2
    by_cases h11 : y < π / 2
    · -- Assume y < π / 2
      have h12 : cos y > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        · linarith [h5, Real.pi_pos, h11]
        · linarith [h11, Real.pi_pos, h6]
      nlinarith [h10, h12]
    · -- Assume y ≥ π / 2
      have h14 : y = π / 2 := by
        linarith [h5, h6]
      exact h14
  linarith [h8, h9, Real.pi_pos]