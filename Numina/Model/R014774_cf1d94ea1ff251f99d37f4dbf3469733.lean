import Mathlib

theorem number_theory_295825 (n : ℕ) :
    Nat.Coprime (21 * n + 4) (14 * n + 3) := by
  have h2 : ∀ n : ℕ, Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
    intro n
    have eq1 : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (14 * n + 3) (7 * n + 1) := by
      rw [show 21 * n + 4 = (14 * n + 3) + (7 * n + 1) by
        omega
      ]
      simp [Nat.gcd_comm]
    have eq2 : Nat.gcd (14 * n + 3) (7 * n + 1) = 1 := by
      have eq3 : Nat.gcd (14 * n + 3) (7 * n + 1) = Nat.gcd (7 * n + 1) (1) := by
        have h3 : (14 * n + 3 : ℕ) = 2 * (7 * n + 1) + 1 := by
          omega
        rw [h3]
        simp [Nat.gcd_comm]
      rw [eq3]
      simp
    rw [eq1, eq2]
  have h2' : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := h2 n
  exact Nat.coprime_iff_gcd_eq_one.mpr h2'