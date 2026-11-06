import Mathlib

theorem number_theory_196322 (p : Fin 24 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hp1 : ∀ i, p i ≥ 5) :
    24 ∣ ∑ i, (p i)^2 := by 
  have h1 : ∀ i, p i % 3 = 1 ∨ p i % 3 = 2 := by 
    intro i
    have h2 : Nat.Prime (p i) := hp i
    have h3 : p i ≥ 5 := hp1 i 
    by_contra h
    push_neg at h 
    have h4 : p i % 3 = 0 := by omega 
    have h5 : p i ≠ 3 := by 
      omega 
    have h6 : ¬ Nat.Prime (p i) := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p i by omega)
      all_goals omega 
    contradiction 
  have h2 : ∀ i, (p i) ^ 2 % 3 = 1 := by
    intro i
    have h1' : p i % 3 = 1 ∨ p i % 3 = 2 := h1 i
    rcases h1' with (h1' | h1')
    · -- Assume p i ≡ 1 (mod 3)
      simp [Nat.pow_mod, h1']
    · -- Assume p i ≡ 2 (mod 3)
      simp [Nat.pow_mod, h1']
  have h3 : ∀ i, (p i) ^ 2 % 8 = 1 := by
    intro i
    have h2' : Nat.Prime (p i) := hp i
    have h3' : p i ≥ 5 := hp1 i 
    have h4 : p i % 2 ≠ 0 := by
      by_contra h
      have h5 : ¬ Nat.Prime (p i) := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p i by omega)
        all_goals omega 
      have h6 : Nat.Prime (p i) := h2'
      contradiction 
    have h4' : p i % 8 = 1 ∨ p i % 8 = 3 ∨ p i % 8 = 5 ∨ p i % 8 = 7 := by 
      omega 
    rcases h4' with (h | h | h | h)
    · -- Assume p i ≡ 1 (mod 8)
      simp [Nat.pow_mod, h]
    · -- Assume p i ≡ 3 (mod 8)
      simp [Nat.pow_mod, h]
    · -- Assume p i ≡ 5 (mod 8)
      simp [Nat.pow_mod, h]
    · -- Assume p i ≡ 7 (mod 8)
      simp [Nat.pow_mod, h]
  have h4 : (∑ i, (p i)^2) % 3 = 0 := by 
    have h5 : ∀ i : Fin 24, (p i) ^ 2 % 3 = 1 := h2 
    simp [Finset.sum_nat_mod, h5, Finset.sum_const, Finset.card_univ]
    <;> omega 
  have h5 : (∑ i, (p i)^2) % 8 = 0 := by 
    have h6 : ∀ i : Fin 24, (p i) ^ 2 % 8 = 1 := h3 
    simp [Finset.sum_nat_mod, h6, Finset.sum_const, Finset.card_univ]
    <;> omega 
  omega