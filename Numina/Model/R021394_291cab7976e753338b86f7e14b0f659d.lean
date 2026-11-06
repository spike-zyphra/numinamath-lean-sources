import Mathlib

theorem number_theory_112885 (n : ℕ) (hn : n ≠ 0) (h1 : Nat.Prime n) (h2 : Nat.Prime (n + 2)) (h3 : Nat.Prime (n + 4)) :
    IsLeast {x | x % n = 1 ∧ x % (n + 2) = 2 ∧ x % (n + 4) = 6} 97 := by 
  have h4 : n ≤ 3 := by
    by_contra h
    push_neg at h
    have h5 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      omega
    rcases h5 with (h8 | h8 | h8)
    · -- `n % 3 = 0`. Hypothesis `h1` says n is prime.
      have h5 : ¬ Nat.Prime n := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ n by omega)
        all_goals omega
      contradiction
    · -- `n % 3 = 1`. `h2` Nat.Prime (n + 2).
      have h7 : (n + 2) % 3 = 0 := by
        omega
      have h7a : ¬ Nat.Prime (n + 2) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n + 2) by omega)
        all_goals omega
      contradiction
    · -- `n % 3 = 2`. `h3` Nat.Prime (n + 4).
      have h7 : (n + 4) % 3 = 0 := by
        omega
      have h7a : ¬ Nat.Prime (n + 4) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (n + 4) by omega)
        all_goals omega
      contradiction
  interval_cases n <;> norm_num at h1 h2 h3 <;> try { 
    constructor
    · -- Show 97 is in the set.
      show (97 : ℕ) % 3 = 1 ∧ (97 : ℕ) % (3 + 2) = 2 ∧ (97 : ℕ) % (3 + 4) = 6
      constructor 
      · -- Show 97 % 3 = 1
        norm_num
      constructor 
      · -- Show 97 % 5 = 2
        norm_num
      · -- Show 97 % 7 = 6
        norm_num 
    · -- Show there is no smaller element in the set.
      intro y hy
      rcases hy with ⟨hy1, hy2, hy3⟩
      by_contra h
      push_neg at h
      have h141 : y % 3 = 1 := hy1
      have h142 : y % 5 = 2 := hy2
      have h143 : y % 7 = 6 := hy3
      omega 
  }