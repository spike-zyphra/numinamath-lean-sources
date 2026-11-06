import Mathlib

theorem algebra_16544 : IsGreatest {n : ℕ | ∃ a : Fin 107 → ℚ, n = ((Finset.univ : Finset (Fin 107)).filter fun i =>
    (∑ i, a i) / 107 < a i).card} 106 := by
  constructor
  · -- Show 106 is in the set.
    use (λ i => if i = 0 then (0 : ℚ) else (1 : ℚ))
    native_decide
  · -- Show no larger element is in the set.
    intro n hn
    rcases hn with ⟨a, ha⟩
    by_contra h
    push_neg at h
    have h1 : ((Finset.univ : Finset (Fin 107)).filter fun i => (∑ j : Fin 107, a j) / 107 < a i).card > 106 := by 
      omega
    have h3 : ((Finset.univ : Finset (Fin 107)).filter fun i => (∑ j : Fin 107, a j) / 107 < a i) = (Finset.univ : Finset (Fin 107)) := by
      have h4 : ((Finset.univ : Finset (Fin 107)).filter fun i => (∑ j : Fin 107, a j) / 107 < a i).card ≥ 107 := by
        have h5 : ((Finset.univ : Finset (Fin 107)).filter fun i => (∑ j : Fin 107, a j) / 107 < a i).card > 106 := h1
        omega
      have h7 : (Finset.univ : Finset (Fin 107)).card = 107 := by
        simp
      have h8 : ((Finset.univ : Finset (Fin 107)).filter fun i => (∑ j : Fin 107, a j) / 107 < a i) ⊆ (Finset.univ : Finset (Fin 107)) := by
        intro i hi
        simp at hi ⊢
      apply Finset.eq_of_subset_of_card_le h8
      omega 
    have h14 : ∀ i : Fin 107, (∑ j : Fin 107, a j) / 107 < a i := by 
      intro i 
      have h3' : i ∈ ((Finset.univ : Finset (Fin 107)).filter fun i0 => (∑ j0 : Fin 107, a j0) / 107 < a i0) := by 
        rw [h3]
        simp 
      simp at h3' ⊢ 
      all_goals try { 
        nlinarith 
      }
    have h15 : ∑ i : Fin 107, a i < ∑ i : Fin 107, a i := by
      have h16 : ∀ i : Fin 107, (∑ j : Fin 107, a j) / 107 < a i := h14
      have h17 : ∑ i : Fin 107, ((∑ j : Fin 107, a j) / 107) < ∑ i : Fin 107, a i := by
        have h18 : ∀ i : Fin 107, (∑ j : Fin 107, a j) / 107 < a i := h16
        have h19 : ∑ i : Fin 107, ((∑ j : Fin 107, a j) / 107) < ∑ i : Fin 107, (a i) := by
          apply Finset.sum_lt_sum
          intro i hi 
          specialize h18 i 
          linarith 
          use ⟨0, by simp⟩
          specialize h18 ⟨0, by simp⟩ 
          simp at h18 ⊢ 
          all_goals try { 
            nlinarith 
          }
        linarith [h19] 
      have h18 : ∑ i : Fin 107, ((∑ j : Fin 107, a j) / 107) = ∑ i : Fin 107, a i := by 
        simp [Finset.sum_const, Finset.card_univ]
        <;> ring
      linarith [h18, h17]
    linarith