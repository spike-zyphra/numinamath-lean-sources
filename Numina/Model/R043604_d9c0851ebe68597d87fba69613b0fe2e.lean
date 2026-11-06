import Mathlib

theorem number_theory_19031 (S : Finset ℕ) (hS : S = {x | x ∈ Finset.Icc 7 12 ∧ ¬∃ y, y ∈ Finset.Icc 1 6 ∧ x * y ≡ 1 [MOD 13]}) :
    S = {12} := by
  have h1 : (12 : ℕ) ∈ (S : Set ℕ) := by
    have h2 : (S : Set ℕ) = {x | x ∈ Finset.Icc 7 12 ∧ ¬∃ y, y ∈ Finset.Icc 1 6 ∧ x * y ≡ 1 [MOD 13]} := by
      exact_mod_cast hS 
    rw [h2]
    simp [Finset.mem_Icc, Nat.ModEq]
    all_goals try native_decide
  have h3 : ∀ (x : ℕ), (x ∈ (S : Set ℕ)) → x = 12 := by 
    intro x hx 
    have hx2 : x ∈ (S : Set ℕ) := by 
      exact hx
    have h4 : x ∈ (S : Set ℕ) := hx2
    have h4' : (x ∈ Finset.Icc 7 12 ∧ ¬∃ y, y ∈ Finset.Icc 1 6 ∧ x * y ≡ 1 [MOD 13]) := by 
      have h5 : (S : Set ℕ) = {x | x ∈ Finset.Icc 7 12 ∧ ¬∃ y, y ∈ Finset.Icc 1 6 ∧ x * y ≡ 1 [MOD 13]} := by 
        exact_mod_cast hS 
      rw [h5] at h4
      exact h4
    rcases h4' with ⟨h6, h7⟩
    have h8 : x ≤ 12 := by
      have h9 : x ∈ Finset.Icc 7 12 := by 
        exact h6
      simp at h9 ⊢
      omega 
    have h10 : x ≥ 7 := by 
      have h9 : x ∈ Finset.Icc 7 12 := by 
        exact h6
      simp at h9 ⊢ 
      omega 
    interval_cases x <;> try { 
      simp [Finset.mem_Icc, Nat.ModEq] at h6 h7 ⊢
      all_goals try tauto 
    }
  have h42 : ∀ x, (x ∈ S) ↔ x = 12 := by
    intro x 
    constructor 
    · -- Assume x ∈ S 
      intro hx 
      have hx2 : x = 12 := by 
        have hx3 : x ∈ (S : Set ℕ) := by 
          exact_mod_cast hx 
        apply h3 x hx3 
      tauto 
    · -- Assume x = 12, prove x ∈ S
      intro h 
      rw [h] 
      have h12 : (12 : ℕ) ∈ S := by 
        have eq3 : (12 : ℕ) ∈ (S : Set ℕ) := h1 
        exact_mod_cast eq3 
      exact h12 
  have h17 : S = {12} := by 
    apply Finset.ext 
    intro x 
    specialize h42 x 
    simpa using h42 
  exact h17