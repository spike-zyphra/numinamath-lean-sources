import Mathlib

theorem number_theory_175256 (n : ℕ) :
    2016 ∣ ((n^2 + n)^2 - (n^2 - n)^2) * (n^6 - 1) := by

  have h1 : ((n^2 + n) ^ 2 - (n^2 - n) ^ 2 : ℕ) = 4 * n^3 := by
    cases n with
    | zero =>
      all_goals
        simp
    | succ n =>
      simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
      <;> ring_nf
      <;> omega
  rw [h1] at *
  have h2 : (n ^ 3 * (n ^ 6 - 1) ) % 7 = 0 := by 
    have h1 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by omega
    rcases h1 with (h | h | h | h | h | h | h) <;> 
      simp [h, Nat.pow_mod, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq] 
  -- Prove divisibility by 8
  have h3 : (n ^ 3 * (n ^ 6 - 1) ) % 8 = 0 := by
    have h1 : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases h1 with (h1 | h1)
    · -- If n is even
      have h2 : n % 8 = 0 ∨ n % 8 = 2 ∨ n % 8 = 4 ∨ n % 8 = 6 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2) <;> simp [h2, Nat.pow_mod, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq]
    · -- If n is odd
      have h4 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
        omega
      rcases h4 with (h4 | h4 | h4 | h4) <;> simp [h4, Nat.pow_mod, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq]
  
  have h4 : (n ^ 3 * (n ^ 6 - 1) ) % 9 = 0 := by
    have h1 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 4 ∨ n % 9 = 5 ∨ n % 9 = 6 ∨ n % 9 = 7 ∨ n % 9 = 8 := by omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> 
      simp [h1, Nat.pow_mod, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq] 
  have h5 : 504 ∣ (n ^ 3 * (n ^ 6 - 1)) := by 
    omega
  -- Now combine with the fact that the expression is divisible by 4 to make it divisible by 2016
  have h7 : 2016 ∣ 4 * n^3 * (n^6 - 1) := by
    have h5' : 504 ∣ (n ^ 3 * (n ^ 6 - 1)) := h5
    have h8 : (4 * n^3 * (n^6 - 1)) % 2016 = 0 := by
      have eq1 : 4 * n^3 * (n^6 - 1) = 4 * (n^3 * (n^6 -1)) := by ring
      rw [eq1] at *
      omega -- uses h5
    exact Nat.dvd_of_mod_eq_zero h8

  exact h7