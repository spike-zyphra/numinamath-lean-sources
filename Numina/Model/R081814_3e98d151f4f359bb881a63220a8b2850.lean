import Mathlib

theorem number_theory_144477 (p : ℕ) (hp : p.Prime) (h : 5 ≤ p) :
    24 ∣ p^2 - 1 := by
  have h1 : p % 2 ≠ 0 := by
    by_contra h2
    have h4 : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals omega
    contradiction
  have h5 : p % 3 ≠ 0 := by
    by_contra h6
    have h7 : 3 ∣ p := by
      omega
    have h8 : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h7 (by omega)
      all_goals omega
    contradiction
  have h6 : p % 2 = 1 := by 
    have h2 : p % 2 ≠ 0 := h1
    omega
  have h7 : p % 3 = 1 ∨ p % 3 = 2 := by 
    have h6 : p % 3 ≠ 0 := h5
    omega
  have h8 : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨ p % 24 = 13 ∨ p % 24 = 17 ∨ p % 24 = 19 ∨ p % 24 = 23 := by
    have h2 : p % 2 = 1 := h6
    have h3 : p % 3 = 1 ∨ p % 3 = 2 := h7
    omega
  rcases h8 with (h | h | h | h | h | h | h | h)
  · -- Case where p % 24 = 1
    have h11 : p % 24 = 1 := h
    have h2 : p ^ 2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h11]
    have : 24 ∣ p ^ 2 - 1 := by
      omega
    exact this
  · -- Case where p % 24 = 5
    have h11 : p % 24 = 5 := h
    have h2 : p ^ 2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h11]
    have : 24 ∣ p ^ 2 - 1 := by
      omega
    exact this
  · -- Case where p % 24 = 7
    have h11 : p % 24 = 7 := h
    have h2 : p ^ 2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h11]
    have : 24 ∣ p ^ 2 - 1 := by
      omega
    exact this
  · -- Case where p % 24 = 11
    have h11 : p % 24 = 11 := h
    have h2 : p ^ 2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h11]
    have : 24 ∣ p ^ 2 - 1 := by
      omega
    exact this
  · -- Case where p % 24 = 13
    have h11 : p % 24 = 13 := h
    have h2 : p ^ 2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h11]
    have : 24 ∣ p ^ 2 - 1 := by
      omega
    exact this
  · -- Case where p % 24 = 17
    have h11 : p % 24 = 17 := h
    have h2 : p ^ 2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h11]
    have : 24 ∣ p ^ 2 - 1 := by
      omega
    exact this
  · -- Case where p % 24 = 19
    have h11 : p % 24 = 19 := h
    have h2 : p ^ 2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h11]
    have : 24 ∣ p ^ 2 - 1 := by
      omega
    exact this
  · -- Case where p % 24 = 23
    have h11 : p % 24 = 23 := h
    have h2 : p ^ 2 % 24 = 1 := by
      norm_num [Nat.pow_mod, h11]
    have : 24 ∣ p ^ 2 - 1 := by
      omega
    exact this