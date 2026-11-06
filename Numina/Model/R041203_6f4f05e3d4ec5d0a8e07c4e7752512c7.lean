import Mathlib

theorem number_theory_161060 (p : Fin 24 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (h : ∀ i, p i ≥ 5) :
    24 ∣ ∑ i, (p i)^2 := by

  have h1 : ∀ i : Fin 24, p i % 2 = 1 := by
    intro i
    have h1 : Nat.Prime (p i) := hp i
    have h2 : p i ≥ 5 := h i
    by_contra h9
    push_neg at h9
    have h3 : p i % 2 = 0 := by omega
    have h4 : ¬ Nat.Prime (p i) := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p i by omega)
      all_goals omega 
    contradiction

  have h2 : ∀ i : Fin 24, (p i) ^ 2 % 8 = 1 := by 
    intro i 
    have h1' : p i % 2 = 1 := h1 i
    have h3 : p i ≥ 5 := h i
    have h4 : (p i) % 8 = 1 ∨ (p i) % 8 = 3 ∨ (p i) % 8 = 5 ∨ (p i) % 8 = 7 := by 
      omega 
    rcases h4 with (h4 | h4 | h4 | h4)
    all_goals 
      simp [h4, Nat.pow_mod]

  have h3 : ∀ i : Fin 24, (p i) ^ 2 % 3 = 1 := by 
    intro i 
    have h1' : Nat.Prime (p i) := hp i 
    have h5 : p i ≥ 5 := h i 
    have h4 : p i % 3 = 1 ∨ p i % 3 = 2 := by
      by_contra h9
      push_neg at h9
      have h0 : p i % 3 = 0 := by omega
      have h4 : ¬ Nat.Prime (p i) := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p i by omega)
        all_goals omega 
      contradiction 
    rcases h4 with (h4 | h4)
    all_goals 
      simp [h4, Nat.pow_mod]

  have h4 : (∑ i : Fin 24, (p i) ^ 2) % 8 = 0 := by
    have h5 : ∀ i : Fin 24, (p i) ^ 2 % 8 = 1 := by 
      intro i 
      exact h2 i 
    simp [Finset.sum_nat_mod, h5, Finset.sum_const, Finset.card_fin]
    <;> try { omega }

  have h6 : (∑ i : Fin 24, (p i) ^ 2) % 3 = 0 := by 
    have h7 : ∀ i : Fin 24, (p i) ^ 2 % 3 = 1 := by 
      intro i 
      exact h3 i 
    simp [Finset.sum_nat_mod, h7, Finset.sum_const, Finset.card_fin]
    <;> try { omega }
  omega