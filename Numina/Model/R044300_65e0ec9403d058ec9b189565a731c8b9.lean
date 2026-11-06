import Mathlib

theorem number_theory_169035 (n : ℕ) (hn : Nat.Prime n) :
    n % 30 = 1 ∨ Nat.Prime (n % 30) := by
  by_cases h : n ≤ 30
  · interval_cases n <;> norm_num at hn ⊢ <;> try { tauto } <;> norm_num
  · -- n > 30
    push_neg at h
    have h1 : n % 2 = 1 := by
      by_contra h1
      push_neg at h1
      have h2 : n % 2 = 0 := by omega
      have h3 : ¬ Nat.Prime n := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ n by omega)
        · omega
        · omega
      contradiction

    have h2 : n % 3 = 1 ∨ n % 3 = 2 := by
      by_contra h2
      push_neg at h2
      have h3 : n % 3 = 0 := by omega
      have h4 : ¬ Nat.Prime n := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ n by omega)
        · omega
        · omega
      contradiction

    have h3 : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      by_contra h3
      push_neg at h3
      have h5' : n % 5 = 0 := by omega
      have h4 : ¬ Nat.Prime n := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ n by omega)
        · omega
        · omega
      contradiction

    -- Solving these congruences using the Chinese Remainder Theorem.
    have h4 : n % 30 = 1 ∨ n % 30 = 7 ∨ n % 30 = 11 ∨ n % 30 = 13 ∨ n % 30 = 17 ∨ n % 30 = 19 ∨ n % 30 = 23 ∨ n % 30 = 29 := by
      omega

    rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4)

    · -- n % 30 = 1
      left
      omega

    · -- n % 30 = 7
      right
      rw [h4]
      norm_num

    · -- n % 30 = 11
      right
      rw [h4]
      norm_num

    · -- n % 30 = 13
      right
      rw [h4]
      norm_num

    · -- n % 30 = 17
      right
      rw [h4]
      norm_num

    · -- n % 30 = 19
      right
      rw [h4]
      norm_num

    · -- n % 30 = 23
      right
      rw [h4]
      norm_num

    · -- n % 30 = 29
      right
      rw [h4]
      norm_num