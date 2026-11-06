import Mathlib

theorem number_theory_250968 :
    IsGreatest {n | 0 < n ∧ n < 500 ∧ ∃ m, 0 < m ∧ m^3 = 6048 * (28^n)} 497 := by
  constructor
  · -- Verify that 497 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Show existence of m
      use 2 ^ 333 * 3 * 7 ^ 166
      constructor
      · -- Verify the constructed m is positive
        native_decide
      · -- Verify the equation holds
        native_decide
  · -- Show for all n in the set, n ≤ 497
    intro n hn
    rcases hn with ⟨hn1, hn2, ⟨m, ⟨hm1, hm2⟩⟩⟩
    by_contra h
    push_neg at h
    -- Determine possible values of n
    have h1 : n ≥ 498 := by omega
    have h2 : n < 500 := by linarith
    have h3 : n = 498 ∨ n = 499 := by omega
    rcases h3 with (r | r)
    · -- Case n = 498
      rw [r] at hm2
      have h4 : m^3 = 6048 * (28 ^ 498) := hm2
      have h5 : m^3 = 2^1001 * 3^3 * 7^499 := by
        norm_num [Nat.pow_mul] at h4 ⊢
        linarith
      have h7 : (m ^ 3).factorization 2 % 3 = 0 := by
        have h8 : (m ^ 3).factorization 2 = 3 * (m.factorization 2) := by
          have h9 : (m ^ 3).factorization 2 = 3 * (m.factorization 2) := by
            simp [Nat.factorization_pow, mul_comm]
          linarith [h9]
        omega
      have h8 : (m ^ 3).factorization 2 = 1001 := by
        have h8 : (m ^ 3) = 2^1001 * 3^3 * 7^499 := by
          linarith [h5]
        have h9 : (m ^ 3).factorization 2 = 1001 := by
          rw [h8]
          native_decide
        exact h9
      omega
    · -- Case n = 499
      rw [r] at hm2
      have h4 : m^3 = 6048 * (28 ^ 499) := hm2
      have h5 : m^3 = 2^1003 * 3^3 * 7^500 := by
        norm_num [Nat.pow_mul] at h4 ⊢
        linarith
      have h7 : (m ^ 3).factorization 2 % 3 = 0 := by
        have h8 : (m ^ 3).factorization 2 = 3 * (m.factorization 2) := by
          have h9 : (m ^ 3).factorization 2 = 3 * (m.factorization 2) := by
            simp [Nat.factorization_pow, mul_comm]
          linarith [h9]
        omega
      have h8 : (m ^ 3).factorization 2 = 1003 := by
        have h8 : (m ^ 3) = 2^1003 * 3^3 * 7^500 := by
          linarith [h5]
        have h9 : (m ^ 3).factorization 2 = 1003 := by
          rw [h8]
          native_decide
        exact h9
      omega