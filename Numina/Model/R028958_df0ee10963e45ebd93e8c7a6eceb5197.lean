import Mathlib

theorem number_theory_161318 : ¬∃ n : ℕ, ∃ k : Fin 99 → ℕ,
    (∀ i, k i > 0) ∧
    (∑ i, k i) = 2020 ∧
    (∀ i, (Nat.digits 10 (k i)).sum = n) := by
  rintro ⟨n, ⟨k, hk_pos, hk_sum, hk_sum2⟩⟩
  have h1 : (∑ i : Fin 99, k i) % 9 = 2020 % 9 := by
    omega
  -- Sum of k i modulo 9.
  have h2 : (∑ i : Fin 99, k i) % 9 = (∑ i : Fin 99, (Nat.digits 10 (k i)).sum) % 9 := by
    have h3 : ∀ i : Fin 99, k i % 9 = (Nat.digits 10 (k i)).sum % 9 := by
      intro i
      have h4 : k i % 9 = (Nat.digits 10 (k i)).sum % 9 := by
        rw [Nat.modEq_nine_digits_sum (k i)]
      omega
    simp [Finset.sum_nat_mod, h3]
  -- Compute the sum of digit sum.
  have h3 : (∑ i : Fin 99, (Nat.digits 10 (k i)).sum) = 99 * n := by
    have h4 : ∀ i : Fin 99, (Nat.digits 10 (k i)).sum = n := by
      intro i
      specialize hk_sum2 i
      simpa using hk_sum2
    simp [Finset.sum_congr, h4, Finset.sum_const, Finset.card_univ]
  -- Compute congruences
  have h4 : (∑ i : Fin 99, (Nat.digits 10 (k i)).sum) % 9 = (99 * n) % 9 := by
    rw [h3]
  have h5 : (2020 : ℕ) % 9 = 4 := by norm_num
  have h6 : (99 * n) % 9 = 0 := by
    have : 99 * n % 9 = 0 := by
      omega
    omega
  omega