import Mathlib

theorem number_theory_275814 (n : ℕ) : 2 ∣ n^2 - n := by
  have h1 : n % 2 = 0 ∨ n % 2 = 1 := by
    omega
  rcases h1 with (even | odd)
  ·
    have h2 : n % 2 = 0 := even
    have h3 : (n ^ 2) % 2 = 0 := by
      simp [Nat.pow_mod, h2]
    have h4 : (n ^ 2 - n) % 2 = 0 := by
      omega
    exact Nat.dvd_of_mod_eq_zero h4
  ·
    have h2 : n % 2 = 1 := odd
    have h3 : (n ^ 2) % 2 = 1 := by
      simp [Nat.pow_mod, h2]
    have h4 : (n ^ 2 - n) % 2 = 0 := by
      omega
    exact Nat.dvd_of_mod_eq_zero h4