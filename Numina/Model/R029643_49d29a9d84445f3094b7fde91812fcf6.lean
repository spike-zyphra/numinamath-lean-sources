import Mathlib

theorem number_theory_146239 (n : ℕ) : 42 ∣ n^7 - n := by
  have h1 : n^7 % 2 = n % 2 := by
    have h2 : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases h2 with (h2 | h2)
    ·
      simp [Nat.pow_mod, h2]
    ·
      simp [Nat.pow_mod, h2]
  have h2 : n^7 % 3 = n % 3 := by
    have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h3 with (h3 | h3 | h3)
    ·
      simp [Nat.pow_mod, h3]
    ·
      simp [Nat.pow_mod, h3]
    ·
      simp [Nat.pow_mod, h3]
  have h3 : n^7 % 7 = n % 7 := by
    have h4 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4)
    all_goals 
      simp [Nat.pow_mod, h4]
  -- Now we need to show that these congruences imply $42 \mid n^7 -n$.
  -- Since 42 is 2*3*7, and we can determine divisibility using the congruences.
  have : 42 ∣ n^7 - n := by
    omega
  exact this