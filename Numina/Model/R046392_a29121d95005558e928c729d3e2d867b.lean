import Mathlib

open Set Real

theorem algebra_269836 {A B : Set ℝ} (fA : ℝ → ℝ)
    (hfA : ∀ x, x ∈ A → fA x = 1) (hfA' : ∀ x, x ∉ A → fA x = 0)
    (fB : ℝ → ℝ) (hfB : ∀ x, x ∈ B → fB x = 1) (hfB' : ∀ x, x ∉ B → fB x = 0) :
    (∀ x, fA x + fB x = 1) ↔ (A ∪ B = ⊤ ∧ A ∩ B = ∅) := by 
  constructor
  · -- Assume $f_A(x) + f_B(x) = 1$ for all $x \in \mathbb{R}$, prove $A \cup B = \mathbb{R}$ and $A \cap B = \emptyset$.
    intro h
    have h1 : A ∪ B = ⊤ := by
      ext x 
      simp only [Set.mem_union, Set.mem_setOf_eq]
      by_contra hx 
      push_neg at hx
      have h2 : x ∉ A := by 
        by_contra h3 
        tauto 
      have h3 : x ∉ B := by 
        by_contra h4 
        tauto 
      have h4 : fA x = 0 := hfA' x h2 
      have h5 : fB x = 0 := hfB' x h3 
      have h6 := h x
      linarith
    have h2 : A ∩ B = ∅ := by 
      ext x 
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h3
      have h4 : x ∈ A := h3.1 
      have h5 : x ∈ B := h3.2 
      have h6 : fA x = 1 := hfA x h4 
      have h7 : fB x = 1 := hfB x h5 
      have h8 := h x 
      linarith 
    constructor 
    · exact h1 
    · exact h2 
  · -- Assume both conditions. Prove $f_A(x) + f_B(x) = 1$ for all $x \in \mathbb{R}$.
    rintro ⟨h1, h2⟩ 
    intro x
    have h3 : x ∈ A ∪ B := by 
      rw [h1] 
      simp 
    rcases h3 with (h4 | h5)
    · -- Case where x ∈ A 
      have h4A : fA x = 1 := hfA x h4
      have h5B : x ∉ B := by 
        by_contra h6
        have h7 : x ∈ A ∩ B := ⟨h4, h6⟩
        rw [h2] at h7 
        simp at h7 
      have h6 : fB x = 0 := hfB' x h5B
      rw [h4A, h6] 
      all_goals norm_num
    · -- Case where x ∈ B 
      have h7B : fB x = 1 := hfB x h5 
      have h8A : x ∉ A := by 
        by_contra h6 
        have h7 : x ∈ A ∩ B := ⟨h6, h5⟩ 
        rw [h2] at h7 
        simp at h7 
      have h9A : fA x = 0 := hfA' x h8A
      rw [h9A, h7B] 
      all_goals norm_num