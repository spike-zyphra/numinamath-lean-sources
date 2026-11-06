import Mathlib

theorem number_theory_122744 (n : ℕ) :
    Nat.Coprime (12 * n + 1) (30 * n + 2) := by
  have h1 : Nat.Coprime (12 * n + 1) (30 * n + 2) := by
    have h3 : Nat.gcd (12 * n + 1) (30 * n + 2) = 1 := by
      have eq1 : Nat.gcd (12 * n + 1) (30 * n + 2) = Nat.gcd (12 * n + 1) (6 * n) := by
        rw [show 30 * n + 2 = 2 * (12 * n + 1) + 6 * n by omega]
        simp [Nat.gcd_add_mul_right_right]
      have eq2 : Nat.gcd (12 * n + 1) (6 * n) = 1 := by
        have eq3 : Nat.gcd (12 * n + 1) (6 * n) = Nat.gcd (6 * n) (1) := by
          rw [show 12 * n + 1 = 2 * (6 * n) + 1 by omega]
          simp [Nat.gcd_add_mul_right_right]
        rw [eq3]
        simp
      rw [eq1, eq2]
    rw [Nat.coprime_iff_gcd_eq_one] at *
    exact h3
  exact h1