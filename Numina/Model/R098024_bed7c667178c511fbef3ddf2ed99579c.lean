import Mathlib

theorem number_theory_150363 {a b : ℕ} : 11 ∣ a^2 + b^2 → 11 ∣ a ∧ 11 ∣ b := by 
  intro h
  have h1 : a % 11 = 0 ∨ a % 11 = 1 ∨ a % 11 = 2 ∨ a % 11 = 3 ∨ a % 11 = 4 ∨ a % 11 = 5 ∨ a % 11 = 6 ∨ a % 11 = 7 ∨ a % 11 = 8 ∨ a % 11 = 9 ∨ a % 11 = 10 := by
    omega
  have h2 : b % 11 = 0 ∨ b % 11 = 1 ∨ b % 11 = 2 ∨ b % 11 = 3 ∨ b % 11 = 4 ∨ b % 11 = 5 ∨ b % 11 = 6 ∨ b % 11 = 7 ∨ b % 11 = 8 ∨ b % 11 = 9 ∨ b % 11 = 10 := by
    omega
  rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1) <;> rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> ( 
    -- Now given specific residues for a and b, compute a^2 + b^2 modulo 11 and show that if the sum is 0, then both must be 0
    try { 
      -- Case where both a % 11 = 0 and b % 11 = 0 
      have ha : a % 11 = 0 := h1
      have hb : b % 11 = 0 := h2
      have h3 : 11 ∣ a := by 
        exact Nat.dvd_of_mod_eq_zero ha
      have h4 : 11 ∣ b := by 
        exact Nat.dvd_of_mod_eq_zero hb
      exact ⟨h3, h4⟩
    }
    all_goals 
      -- Case where both a and b are not 0 mod 11, compute the sum of squares modulo 11 
      norm_num [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, h1, h2] at h <;> omega 
    -- This will either lead to a contradiction or prove divisibility
  ) <;> try { contradiction }