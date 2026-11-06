import Mathlib

theorem number_theory_203057 (x : ℕ) : Nat.Coprime (27 * x + 4) (18 * x + 3) := by
  have h1 : Nat.gcd (27 * x + 4) (18 * x + 3) = 1 := by
    -- Prove that GCD divides both expressions
    have eq1 : Nat.gcd (27 * x + 4) (18 * x + 3) ∣ (27 * x + 4) := by
      exact Nat.gcd_dvd_left (27 * x + 4) (18 * x + 3)
    have eq2 : Nat.gcd (27 * x + 4) (18 * x + 3) ∣ (18 * x + 3) := by
      exact Nat.gcd_dvd_right (27 * x + 4) (18 * x + 3)
    -- Prove that GCD divides 1 using the linear combination.
    -- We know that 1 = 3*(18x+3) - 2*(27x+4).
    have eq3 : Nat.gcd (27 * x + 4) (18 * x + 3) ∣ (1 : ℕ) := by
      have h2 : Nat.gcd (27 * x + 4) (18 * x + 3) ∣ (3 * (18 * x + 3) - 2 * (27 * x + 4) : ℕ) := by
        apply Nat.dvd_sub'
        · -- Show that gcd (27 * x + 4) (18 * x + 3) divides 3 * (18 * x + 3)
          apply Dvd.dvd.mul_left
          exact eq2
        · -- Show that gcd (27 * x + 4) (18 * x + 3) divides 2 * (27 * x + 4)
          apply Dvd.dvd.mul_left
          exact eq1
      have h3 : (3 * (18 * x + 3) - 2 * (27 * x + 4) : ℕ) = 1 := by
        omega
      rw [h3] at h2
      exact h2
    -- Since the GCD divides 1, the GCD must be 1
    have eq4 : Nat.gcd (27 * x + 4) (18 * x + 3) ≤ (1 : ℕ) := by
      exact Nat.le_of_dvd (by norm_num) eq3
    -- The GCD is at least 1 since both numbers are positive
    have h5 : Nat.gcd (27 * x + 4) (18 * x + 3) ≥ 1 := by
      have h1 : (27 * x + 4 : ℕ) > 0 := by
        omega
      have h2 : (18 * x + 3 : ℕ) > 0 := by
        omega
      have h3 : Nat.gcd (27 * x + 4) (18 * x + 3) > 0 := by
        apply Nat.gcd_pos_of_pos_left
        omega
      linarith
    -- The GCD is at most 1 and at least 1, so it must be 1.
    linarith
  -- The numbers are coprime if their GCD is 1 (definition in Lean)
  rw [Nat.coprime_iff_gcd_eq_one]
  exact h1