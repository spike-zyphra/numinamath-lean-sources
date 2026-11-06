import Mathlib

theorem number_theory_324261 {n : ℕ} (hn : n > 11) :
    ∃ c1 c2, c1 + c2 = n ∧ c1 ≠ 1 ∧ c2 ≠ 1 ∧ ¬Nat.Prime c1 ∧ ¬Nat.Prime c2 := by
  have h1 : n > 11 := hn
  by_cases h : n % 2 = 0
  · -- Case n is even.
    have h2 : ∃ k, n = 2 * k := by 
      refine' ⟨n / 2, by omega⟩
    rcases h2 with ⟨k, hk⟩
    use 4
    use n - 4
    constructor
    · -- Show that 4 + (n - 4) = n
      omega
    constructor
    · -- Show that 4 ≠ 1
      norm_num
    constructor
    · -- Show that n - 4 ≠ 1
      omega
    constructor
    · -- Show that ¬Nat.Prime 4
      norm_num
    · -- Show that ¬Nat.Prime (n - 4)
      have h3 : n - 4 > 7 := by omega
      have h4 : (n - 4) % 2 = 0 := by
        omega
      have h6 : ¬Nat.Prime (n - 4) := by
        by_contra h7
        have h8 : ¬Nat.Prime (n - 4) := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (n - 4) by omega) (by omega) (by omega)
        contradiction
      exact h6
  · -- Case n is odd.
    have h2 : n % 2 = 1 := by 
      omega
    use 9
    use n - 9
    constructor
    · -- Show that 9 + (n - 9) = n
      omega
    constructor
    · -- Show that 9 ≠ 1
      norm_num
    constructor
    · -- Show that n - 9 ≠ 1
      omega
    constructor
    · -- Show that ¬Nat.Prime 9
      norm_num
    · -- Show that ¬Nat.Prime (n - 9)
      have h3 : n - 9 ≥ 4 := by omega
      have h4 : (n - 9) % 2 = 0 := by
        omega
      have h6 : ¬Nat.Prime (n - 9) := by
        by_contra h7
        have h8 : ¬Nat.Prime (n - 9) := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (n - 9) by omega) (by omega) (by omega)
        contradiction
      exact h6