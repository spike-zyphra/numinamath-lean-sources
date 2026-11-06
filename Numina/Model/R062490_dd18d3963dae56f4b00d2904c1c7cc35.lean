import Mathlib

theorem number_theory_144465 (n : ℕ) : 6 ∣ n^3 - n := by
  have h5 : n^3 % 6 = n % 6 := by
    have h6 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
    cases h6 with
    | inl h6 =>
      simp [h6, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
    | inr h6 =>
      cases h6 with
      | inl h6 =>
        simp [h6, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
      | inr h6 =>
        cases h6 with
        | inl h6 =>
          simp [h6, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
        | inr h6 =>
          cases h6 with
          | inl h6 =>
            simp [h6, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
          | inr h6 =>
            cases h6 with
            | inl h6 =>
              simp [h6, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
            | inr h6 =>
              simp [h6, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
  exact Nat.dvd_of_mod_eq_zero (by omega)