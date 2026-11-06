import Mathlib

theorem number_theory_6861 : {x | x > 0 ∧ x % 2 = 1 ∧ x % 5 = 2 ∧ x % 7 = 3 ∧ x % 9 = 4} = {157 + 630 * k | k : ℕ} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Proof of the forward direction: if x in the set of integers satisfying the congruences, then it's in the set {157+630*k} 
    intro h
    rcases h with ⟨hx_pos, h1, h2, h3, h4⟩
    have h5 : x % 2 = 1 := h1
    have h6 : x % 5 = 2 := h2
    have h7 : x % 7 = 3 := h3
    have h8 : x % 9 = 4 := h4
    have h9 : x ≥ 1 := by
      omega
    have : ∃ k : ℕ, x = 157 + 630 * k := by 
      have h10 : x % 630 = 157 := by 
        omega
      refine ⟨x / 630, by 
        omega
      ⟩
    rcases this with ⟨k, hk⟩
    refine ⟨k, by 
      linarith
    ⟩
  · -- Proof of the reverse direction: if x in the set {157+630*k}, then it's in the set of integers satisfying the congruences
    rintro ⟨k, rfl⟩
    constructor 
    · -- Show that x is positive 
      omega 
    constructor 
    · -- Show that x % 2 = 1 
      omega 
    constructor 
    · -- Show that x % 5 = 2 
      omega 
    constructor 
    · -- Show that x % 7 = 3 
      omega 
    · -- Show that x % 9 = 4 
      omega