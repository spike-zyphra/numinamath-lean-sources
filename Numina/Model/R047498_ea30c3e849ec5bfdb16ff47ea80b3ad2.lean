import Mathlib

theorem algebra_18821 (A : Finset (Finset ℕ)) (hA : A.card = 15)
    (hA1 : ∀ s ∈ A, s.card = 2) (hA2 : ∀ s ∈ A, s ⊆ Finset.Icc 1 6) :
    ∑ s ∈ A, (s.sum id) = 105 := by
  have h1 : A = Finset.powersetCard 2 (Finset.Icc 1 6) := by
    have h2 : A.card = 15 := hA
    have h3 : Finset.card (Finset.powersetCard 2 (Finset.Icc 1 6)) = 15 := by
      rw [Finset.card_powersetCard]
      all_goals native_decide
    have h4 : A ⊆ Finset.powersetCard 2 (Finset.Icc 1 6) := by
      intro s hs
      have hs1 : s.card = 2 := hA1 s hs
      have hs2 : s ⊆ Finset.Icc 1 6 := hA2 s hs
      simp [Finset.mem_powersetCard] at *
      all_goals
        try { tauto }
    have h6 : Finset.card (A) = Finset.card (Finset.powersetCard 2 (Finset.Icc 1 6)) := by
      rw [hA, h3]
    have h7 : A = Finset.powersetCard 2 (Finset.Icc 1 6) := by
      apply Finset.eq_of_subset_of_card_le h4
      rw [h6]
      all_goals try { simp }
    exact h7
  rw [h1]
  native_decide