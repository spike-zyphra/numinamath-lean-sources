import Mathlib

theorem number_theory_23204 (n : ℕ) (hn : n > 0) :
    IsLeast {x | ∃ s : Finset ℕ, ∑ i ∈ s, i = x ∧ ∏ i ∈ s, i = 84} 14 := by 
  constructor
  · -- Show 14 is in the set
    use {3, 4, 7}
    all_goals 
      native_decide
  · -- Show that 14 is the least such
    intro x hx 
    rcases hx with ⟨s, h1, h2⟩
    have h3 : x ≥ 14 := by 
      have h4 : ∏ i ∈ s, i = 84 := h2
      have h5 : ∑ i ∈ s, i = x := h1
      have h6 : s ⊆ Finset.filter (fun i => i ∣ 84) (Finset.Icc 0 84) := by
        intro i hi
        simp at hi ⊢
        have h6 : i ∣ 84 := by
          have h7 : i ∈ s := hi
          have h8 : i ∣ 84 := by
            have h9 : i ∈ s := h7
            have h10 : ∏ j ∈ s, j = 84 := h4
            have h11 : i ∣ ∏ j ∈ s, j := by
              apply Finset.dvd_prod_of_mem
              exact h9
            rw [h10] at h11
            exact h11
          exact h8
        have h7 : i ≤ 84 := by 
          have h6' : i ∣ 84 := h6
          exact Nat.le_of_dvd (by norm_num) h6'
        tauto
      have h7 : s ∈ (Finset.powerset (Finset.filter (fun i => i ∣ 84) (Finset.Icc 0 84))).filter (fun s => ∏ i ∈ s, i = 84) := by 
        simp [h4]
        <;> try tauto
        <;> try try { native_decide }
      have h8 : ∀ s ∈ (Finset.powerset (Finset.filter (fun i => i ∣ 84) (Finset.Icc 0 84))).filter (fun s => ∏ i ∈ s, i = 84), ∑ i ∈ s, i ≥ 14 := by 
        native_decide
      have h9 : ∑ i ∈ s, i ≥ 14 := by 
        apply h8 
        exact h7 
      linarith [h5, h9]
    linarith