import Mathlib

open Set Real

theorem algebra_216851 {a : ℝ} (M : Set ℝ) (hM : M = {x | 2 - a ≤ x ∧ x ≤ 1 + a}) :
    {x | 1 ≤ x ∧ x ≤ 2} ∩ M = {x | 1 ≤ x ∧ x ≤ 2} ↔ 1 ≤ a := by
  constructor
  · -- Forward direction: {x | 1 ≤ x ∧ x ≤ 2} ∩ M = {x | 1 ≤ x ∧ x ≤ 2} → 1 ≤ a
    intro h
    have h1 : (1 : ℝ) ∈ {x | 1 ≤ x ∧ x ≤ 2} := by
      exact ⟨by norm_num, by norm_num⟩
    have h2 : (1 : ℝ) ∈ {x | 1 ≤ x ∧ x ≤ 2} ∩ M := by
      rw [h]
      exact h1
    have h3 : (1 : ℝ) ∈ M := by
      exact h2.2
    have h4 : (1 : ℝ) ≤ 1 + a := by
      rw [hM] at h3
      have h5 : (1 : ℝ) ≤ 1 + a := by
        simp at h3 ⊢
        linarith
      linarith
    have h5 : 2 - a ≤ (1 : ℝ) := by
      rw [hM] at h3
      have h6 : 2 - a ≤ (1 : ℝ) := by
        simp at h3 ⊢
        linarith
      linarith
    have h7 : 1 ≤ a := by
      nlinarith
    exact h7
  · -- Backward direction: 1 ≤ a → {x | 1 ≤ x ∧ x ≤ 2} ∩ M = {x | 1 ≤ x ∧ x ≤ 2}
    intro h
    ext x
    simp only [hM, Set.mem_inter, Set.mem_setOf_eq]
    constructor
    · -- First direction: membership in intersection implies membership in the set
      intro h
      exact h.1
    · -- Second direction: membership in the set implies membership in intersection
      intro h
      have h1 : 1 ≤ x := h.1
      have h2 : x ≤ 2 := h.2
      have h3 : 2 - a ≤ x := by 
          nlinarith 
      have h4 : x ≤ 1 + a := by 
          nlinarith 
      constructor 
      · -- Show x ∈ {x | 1 ≤ x ∧ x ≤ 2}
        exact h
      · -- Show 2 - a ≤ x ∧ x ≤ 1 + a
        exact ⟨h3, h4⟩