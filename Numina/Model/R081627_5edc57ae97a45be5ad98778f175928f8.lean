import Mathlib

theorem number_theory_275905 (n : ℕ) (hn : n.Prime) (hne2 : n ≠ 2) (hne3 : n ≠ 3) :
    24 ∣ (n^2 - 1) := by
  have h1 : n ≥ 4 := by
    by_contra h
    push_neg at h
    have : n < 4 := by linarith
    interval_cases n <;> norm_num at hn hne2 hne3
  have h2 : n % 2 ≠ 0 := by
    by_contra h
    have h4 : ¬ n.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ n by omega)
      all_goals
        omega
    contradiction
  have h3 : n % 3 ≠ 0 := by
    by_contra h'
    have h4 : 3 ∣ n := by omega
    have h5 : ¬ n.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ n by omega)
      all_goals 
        omega
    contradiction
  have h5 : n % 2 = 1 := by
    omega
  have h6 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    omega
  have h8 : (n ^ 2) % 8 = 1 := by
    rcases h6 with (h | h | h | h) <;> norm_num [Nat.pow_mod, h] 
  have h9 : (n ^ 2) % 3 = 1 := by
    have h4 : n % 3 = 1 ∨ n % 3 = 2 := by 
      omega
    rcases h4 with (h | h) <;> norm_num [Nat.pow_mod, h] 
  -- use the Chinese Remainder Theorem
  have h24 : 24 ∣ (n^2 - 1) := by
    omega
  exact h24