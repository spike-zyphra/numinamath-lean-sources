import Mathlib

theorem number_theory_240358 (n : ℕ) (hn : Nat.Prime n) (hne2 : n ≠ 2) (hne3 : n ≠ 3) :
    24 ∣ (n ^ 2 - 1) := by
  have h1 : n ≥ 4 := by
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn hne2 hne3
  have h2 : n ≥ 5 := by
    by_contra h
    push_neg at h
    have h3 : n < 5 := by linarith
    interval_cases n <;> norm_num at hn hne2 hne3
  have h5 : n % 2 ≠ 0 := by
    by_contra h
    have : ¬ Nat.Prime n := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ n by omega) (by omega) (by omega)
    contradiction
  have h5' : n % 3 ≠ 0 := by
    by_contra h
    have : ¬ Nat.Prime n := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ n by omega) (by omega) (by omega)
    contradiction
  have h3 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by 
    omega
  have h8 : (n ^ 2) % 8 = 1 := by
    rcases h3 with (h | h | h | h)
    · simp [Nat.pow_mod, h]
    · simp [Nat.pow_mod, h]
    · simp [Nat.pow_mod, h]
    · simp [Nat.pow_mod, h]
  have h4 : n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  have h3' : (n ^ 2) % 3 = 1 := by 
    rcases h4 with (h | h)
    · simp [Nat.pow_mod, h]
    · simp [Nat.pow_mod, h]
  have hdiv : (n ^ 2 - 1) % 24 = 0 := by
    omega
  exact Nat.dvd_of_mod_eq_zero hdiv