import Mathlib

theorem number_theory_174644 (n : ℕ) (h₀ : ¬ 3 ∣ n) (h₁ : ¬ 3 ∣ n + 1) :
    3 ∣ n + (n + 1) := by
  have h2 : n % 3 = 1 := by
    have h3 : n % 3 ≠ 0 := by 
      intro h
      have h6 : 3 ∣ n := by
        exact Nat.dvd_of_mod_eq_zero h
      contradiction
    have h4 : n % 3 ≠ 2 := by
      intro h
      have h8 : 3 ∣ n + 1 := by
        have : (n + 1) % 3 = 0 := by 
          omega
        exact Nat.dvd_of_mod_eq_zero this
      contradiction
    -- We know that it is none of the residues. Therefore it must be 1.
    -- There are these possibilities.
    have : n % 3 = 1 := by
      omega
    assumption
  -- So now that n % 3 = 1, we compute that the sum is divisible by 3.
  -- Compute that n + (n + 1) % 3 = 0.
  have h3 : (n + (n + 1)) % 3 = 0 := by
    simp [Nat.add_mod, h2]
    all_goals omega
  exact Nat.dvd_of_mod_eq_zero h3