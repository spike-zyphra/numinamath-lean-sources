import Mathlib

theorem number_theory_257016 (p : Fin 24 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hp1 : ∀ i, p i ≥ 5) :
    24 ∣ ∑ i, (p i)^2 := by
  have h1 : ∀ i, p i % 3 = 1 ∨ p i % 3 = 2 := by
    intro i
    have h1 : Nat.Prime (p i) := hp i
    have h2 : p i ≥ 5 := hp1 i
    have h3 : p i % 3 ≠ 0 := by
      by_contra h
      have h4 : ¬Nat.Prime (p i) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p i by omega) (by omega) (by omega)
      contradiction
    omega
  have h2 : ∀ i, (p i)^2 % 3 = 1 := by
    intro i
    have h1' : p i % 3 = 1 ∨ p i % 3 = 2 := h1 i
    rcases h1' with (h1' | h1')
    · simp [Nat.pow_mod, h1']
    · simp [Nat.pow_mod, h1']
  have h3 : ∀ i, (p i)^2 % 8 = 1 := by
    intro i
    have h4 : p i % 2 = 1 := by
      have h4 : Nat.Prime (p i) := hp i
      have h2 : p i ≥ 5 := hp1 i
      have h3 : p i % 2 = 1 := by
        by_contra h
        push_neg at h
        have h4 : ¬Nat.Prime (p i) := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p i by omega) (by omega) (by omega)
        contradiction
      omega
    have h6 : (p i)^2 % 8 = 1 := by
      have h5 : p i % 8 = 1 ∨ p i % 8 = 3 ∨ p i % 8 = 5 ∨ p i % 8 = 7 := by
        omega
      rcases h5 with (h5 | h5 | h5 | h5)
      · simp [Nat.pow_mod, h5]
      · simp [Nat.pow_mod, h5]
      · simp [Nat.pow_mod, h5]
      · simp [Nat.pow_mod, h5]
    exact h6
  have h5 : (∑ i, (p i)^2) % 3 = 0 := by
    have h6 : ∀ i : Fin 24, (p i)^2 % 3 = 1 := h2
    have h7' : (∑ i, (p i)^2) % 3 = (∑ i, ((p i)^2) % 3) % 3 := by
      simp [Finset.sum_nat_mod]
    have h7 : (∑ i, ((p i)^2) % 3) = 24 := by
      have h8 : ∀ i : Fin 24, (p i)^2 % 3 = 1 := h6
      simp_all [Finset.sum_const, Finset.card_univ]
    rw [h7'] 
    omega
  have h6 : (∑ i, (p i)^2) % 8 = 0 := by
    have h7 : ∀ i : Fin 24, (p i)^2 % 8 = 1 := h3
    have h8' : (∑ i, (p i)^2) % 8 = (∑ i, ((p i)^2) % 8) % 8 := by
      simp [Finset.sum_nat_mod]
    have h8 : (∑ i, ((p i)^2) % 8) = 24 := by
      have h9 : ∀ i : Fin 24, (p i)^2 % 8 = 1 := h7
      simp_all [Finset.sum_const, Finset.card_univ]
    rw [h8']
    omega
  have h7 : ∃ k, ∑ i, (p i)^2 = 8 * k := by
    have h8 : (∑ i, (p i)^2) % 8 = 0 := h6
    refine' ⟨(∑ i, (p i)^2) / 8, by omega⟩
  rcases h7 with ⟨k, hk⟩
  have h8 : (∑ i, (p i)^2 : ℕ) % 3 = 0 := h5
  rw [hk] at h8
  have h9 : (8 * k : ℕ) % 3 = 0 := h8
  have h10 : k % 3 = 0 := by
    omega
  have h11 : ∃ m : ℕ, k = 3 * m := by
    refine' ⟨k / 3, by omega⟩
  rcases h11 with ⟨m, hm⟩
  subst k
  have h9 : 24 ∣ ∑ i, (p i)^2 := by
    use m
    all_goals omega
  exact h9