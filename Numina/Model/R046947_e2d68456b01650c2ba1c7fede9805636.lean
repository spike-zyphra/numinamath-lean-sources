import Mathlib

theorem number_theory_223264 (n : ℕ) :
    Nat.Coprime (21*n + 4) (14*n + 3) := by
  have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
    have gcd1 : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (14 * n + 3) (7 * n + 1) := by
      have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (14 * n + 3) (21 * n + 4) := by
        rw [Nat.gcd_comm]
      have h2 : Nat.gcd (14 * n + 3) (21 * n + 4) = Nat.gcd (14 * n + 3) (7 * n + 1) := by
        have h3 : 21 * n + 4 = (14 * n + 3) + (7 * n + 1) := by 
          omega
        rw [h3]
        simp [Nat.gcd_comm]
        all_goals omega
      rw [h1, h2]
    have gcd2 : Nat.gcd (14 * n + 3) (7 * n + 1) = 1 := by
      have g2 : 14 * n + 3 = 2 * (7 * n + 1) + 1 := by
        omega
      have g3 : Nat.gcd (14 * n + 3) (7 * n + 1) = Nat.gcd (7 * n + 1) 1 := by
        rw [show 14 * n + 3 = 2 * (7 * n + 1) + 1 by omega]
        simp [Nat.gcd_comm]
      rw [g3]
      simp
    rw [gcd1]
    exact gcd2
  rw [Nat.coprime_iff_gcd_eq_one]
  exact h1