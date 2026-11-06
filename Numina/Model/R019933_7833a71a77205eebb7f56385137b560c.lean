import Mathlib

theorem number_theory_291350 : ∀ n : ℕ, Nat.Coprime (21*n+4) (14*n+3) := by
  intro n
  have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by 
    have h2 : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (14 * n + 3) (7 * n + 1) := by 
      rw [show 21 * n + 4 = (14 * n + 3) + (7 * n + 1) by omega]
      simp [Nat.gcd_comm]
    rw [h2]
    have h4 : (14 * n + 3) = 2 * (7 * n + 1) + 1 := by 
      omega
    rw [h4]
    simp [Nat.gcd_comm]
  rw [Nat.coprime_iff_gcd_eq_one]
  exact h1