import Mathlib


theorem algebra_15199 (a : Fin 5 → ℕ) (ha : ∀ i, 0 < a i)
    (h : Even (∏ i, a i)) :
    {i | Odd (a i)}.encard ≤ 4 := by
  have h1 : {i | Odd (a i)} = ↑(Finset.filter (fun i => Odd (a i)) Finset.univ) := by
    ext i
    simp
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  have h2 : (Finset.filter (fun i : Fin 5 => Odd (a i)) Finset.univ).card ≤ 4 := by
    by_contra h9
    push_neg at h9
    have h10 : (Finset.filter (fun i : Fin 5 => Odd (a i)) Finset.univ).card ≥ 5 := by
      omega
    have h11 : ∀ i : Fin 5, Odd (a i) := by
      intro i
      have h13 : i ∈ (Finset.filter (fun i : Fin 5 => Odd (a i)) Finset.univ) := by
        have h100 : (Finset.filter (fun i : Fin 5 => Odd (a i)) Finset.univ).card = 5 := by
          have h17 : (Finset.filter (fun i : Fin 5 => Odd (a i)) Finset.univ).card ≤ 5 := by
            have h94 : (Finset.filter (fun i : Fin 5 => Odd (a i)) Finset.univ) ⊆ Finset.univ := by
              intro x hx
              simp at hx ⊢
            have h95 : (Finset.filter (fun i : Fin 5 => Odd (a i)) Finset.univ).card ≤ (Finset.univ : Finset (Fin 5)).card := by
              apply Finset.card_le_card
              exact h94
            have h96 : (Finset.univ : Finset (Fin 5)).card = 5 := by
              simp [Finset.card_univ]
            omega
          omega
        have h101 : (Finset.filter (fun i : Fin 5 => Odd (a i)) Finset.univ) = Finset.univ := by
          have h100 : (Finset.filter (fun i : Fin 5 => Odd (a i)) Finset.univ).card = 5 := by
            omega
          have h103 : (Finset.filter (fun i : Fin 5 => Odd (a i)) Finset.univ) ⊆ Finset.univ := by
            intro x hx
            simp at hx ⊢
          have h104 : (Finset.filter (fun i : Fin 5 => Odd (a i)) Finset.univ).card = (Finset.univ : Finset (Fin 5)).card := by
            have h96 : (Finset.univ : Finset (Fin 5)).card = 5 := by
              simp [Finset.card_univ]
            rw [h96] at *
            omega
          have h105 : (Finset.filter (fun i : Fin 5 => Odd (a i)) Finset.univ) = (Finset.univ : Finset (Fin 5)) := by
            apply Finset.eq_of_subset_of_card_le h103
            rw [h104]
          exact h105
        simp [h101] at *
      simp at h13 ⊢
      tauto
    -- Therefore, all a i's are odd
    have h150 : ∀ i : Fin 5, (a i) % 2 = 1 := by
      intro i
      have h16 : Odd (a i) := h11 i
      rcases h16 with ⟨k, hk⟩
      omega
    -- Now, the product of five odd numbers must be odd
    have h170 : (∏ i : Fin 5, a i) % 2 = 1 := by
      simp [Finset.prod_nat_mod, h150]
    -- But the given hypothesis is that the product is even
    have h6 : (∏ i : Fin 5, a i) % 2 = 0 := by
      obtain ⟨k, hk⟩ := h
      omega
    omega
  exact_mod_cast h2