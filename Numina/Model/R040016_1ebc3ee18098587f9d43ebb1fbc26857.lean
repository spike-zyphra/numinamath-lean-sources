import Mathlib

theorem number_theory_142889 (S : Finset ℕ) (hS : S.card = 2023) :
    ∀ m ∈ S, ∀ n ∈ S, m ≠ n → (Nat.factorization (m - n) 2022) ≤ 2023 := by
  intro m hm n hn hmn
  have h1 : Nat.factorization (m - n) 2022 = 0 := by
    have h2 : ¬ (Nat.Prime 2022) := by
      norm_num
    have h4 : ¬ (Nat.Prime 2022) := h2
    have h5 : Nat.factorization (m - n) 2022 = 0 := by 
      apply Nat.factorization_eq_zero_of_non_prime
      exact h4
    exact h5
  omega