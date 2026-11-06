import Mathlib

theorem number_theory_3487 : IsGreatest {k | ∃ s : Finset ℤ, s.card = k ∧ ¬ IsSquare (∏ x ∈ s, x) ∧ s ⊆ Finset.Icc (-16) 16} 31 := by 
  constructor 
  · -- Let's prove 31 is in the set 
    use Finset.Icc (-16) (-2) ∪ Finset.Icc 1 16 
    native_decide 
  · -- Let's prove that for any k in the set, k ≤ 31 
    intro k hk 
    rcases hk with ⟨s, hs1, hs2, hs3⟩ 
    by_contra h 
    push_neg at h 
    have h2 : k ≥ 32 := by linarith 
    have h3 : s.card ≥ 32 := by 
      omega 
    by_cases h0 : (0 : ℤ) ∈ s 
    · -- If 0 ∈ s, then the product is 0, which is a square 
      have h_zero : (∏ x ∈ s, x) = 0 := by 
        apply Finset.prod_eq_zero_iff.mpr 
        refine ⟨0, by simp [h0], by simp [h0]⟩ 
      have h3' : IsSquare (∏ x ∈ s, x) := by 
        rw [h_zero] 
        exact ⟨0, by norm_num⟩ 
      have h3not : ¬ IsSquare (∏ x ∈ s, x) := hs2 
      contradiction 
    · -- 0 ∉ s 
      have h0' : (0 : ℤ) ∉ s := by 
        intro h 
        tauto 
      have h4 : s.card ≤ 32 := by 
        have h5 : s ⊆ Finset.Icc (-16) 16 := by 
          exact_mod_cast hs3 
        have h6 : s ⊆ (Finset.Icc (-16 : ℤ) 16) \ {0} := by 
          intro x hx 
          have h7 : x ∈ Finset.Icc (-16 : ℤ) 16 := by 
            apply h5 hx 
          have h7' : x ≠ 0 := by 
            intro h 
            have h8 : x = (0 : ℤ) := by linarith 
            rw [h8] at hx 
            tauto 
          simp at *
          tauto 
        have h7 : ((Finset.Icc (-16 : ℤ) 16) \ {0}).card = 32 := by 
          native_decide 
        have h8 : s.card ≤ ((Finset.Icc (-16 : ℤ) 16) \ {0}).card := by 
          apply Finset.card_le_card 
          exact h6 
        rw [h7] at h8 
        linarith 
      have h5' : s.card = 32 := by 
        linarith 
      have h6 : s = (Finset.Icc (-16 : ℤ) (-1)) ∪ (Finset.Icc (1 : ℤ) 16) := by 
        have h7 : s.card = 32 := h5' 
        have h8 : s ⊆ (Finset.Icc (-16 : ℤ) (-1)) ∪ (Finset.Icc (1 : ℤ) 16) := by 
          intro x hx 
          have h9 : x ∈ s := hx 
          have h10 : x ∈ Finset.Icc (-16) 16 := by 
            apply hs3 hx 
          have h11 : x ≠ 0 := by 
            intro h 
            have h12 : x = (0 : ℤ) := by linarith 
            rw [h12] at hx 
            tauto 
          simp at h10 ⊢ 
          omega 
        have h9 : ((Finset.Icc (-16 : ℤ) (-1)) ∪ (Finset.Icc (1 : ℤ) 16)).card = 32 := by 
          native_decide 
        have h10 : s = (Finset.Icc (-16 : ℤ) (-1)) ∪ (Finset.Icc (1 : ℤ) 16) := by 
          apply Finset.eq_of_subset_of_card_le h8 
          all_goals 
            simp_all 
        exact h10 
      have h_zero : IsSquare (∏ x ∈ s, x) := by 
        rw [h6] 
        native_decide 
      have h3not : ¬ IsSquare (∏ x ∈ s, x) := hs2 
      contradiction