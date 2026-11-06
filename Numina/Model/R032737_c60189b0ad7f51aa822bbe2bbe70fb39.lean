import Mathlib

theorem number_theory_66780 (n : ℕ) (hn : 0 < n) (p : Fin n → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hpi : ∀ i, p i > 5)
    (h : 6 ∣ ∑ i, (p i)^2) : 6 ∣ n := by

  have h1 : ∀ i, (p i) % 6 = 1 ∨ (p i) % 6 = 5 := by
    intro i
    have h1 : Nat.Prime (p i) := hp i
    have h2 : p i > 5 := hpi i
    have h3 : (p i) % 2 ≠ 0 := by
      by_contra h4
      have h4' : ¬ Nat.Prime (p i) := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p i by omega)
        all_goals linarith
      contradiction
    have h4 : (p i) % 3 ≠ 0 := by
      by_contra h4
      have h4' : ¬ Nat.Prime (p i) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p i by omega)
        all_goals linarith
      contradiction
    omega
  have h1sq : ∀ i, (p i) ^ 2 % 6 = 1 := by
    intro i
    have h1_i : (p i) % 6 = 1 ∨ (p i) % 6 = 5 := h1 i
    rcases h1_i with (h1_i | h1_i)
    · -- case where $p_i \equiv 1 \pmod{6}$
      simp [Nat.pow_mod, h1_i]
    · -- case where $p_i \equiv 5 \pmod{6}$
      simp [Nat.pow_mod, h1_i]
      all_goals omega
  have h2 : (∑ i : Fin n, (p i) ^ 2) % 6 = n % 6 := by
    have h1sq' : ∀ (i : Fin n), (p i) ^ 2 % 6 = 1 := h1sq
    have h4 : ((∑ i : Fin n, (p i) ^ 2) % 6) = (n % 6 : ℕ) := by
      -- Use properties of summation modulo
      have h5 : (∑ i : Fin n, (p i) ^ 2) % 6 = (∑ i : Fin n, ((p i) ^ 2) % 6) % 6 := by
        simp [Finset.sum_nat_mod]
      rw [h5]
      have h6 : ∑ i : Fin n, ((p i) ^ 2) % 6 = ∑ i : Fin n, (1 : ℕ) := by
        apply Finset.sum_congr
        · -- Show that the index set is the same
          rfl
        · -- Show that each term is equal
          intro i hi
          exact h1sq' i
      rw [h6]
      simp
      all_goals omega
    exact h4
  have : n % 6 = 0 := by
    have h2' : (∑ i : Fin n, (p i) ^ 2) % 6 = 0 := by
      omega
    omega
  exact Nat.dvd_of_mod_eq_zero this