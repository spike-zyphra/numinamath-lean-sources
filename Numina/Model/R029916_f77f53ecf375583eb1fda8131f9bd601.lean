import Mathlib


theorem number_theory_32910 (n : ℕ) :
    Nat.Coprime (21*n+4) (14*n+3) := by 
  rw [Nat.coprime_iff_gcd_eq_one]
  have h2 : Nat.gcd (21*n + 4) (14*n + 3) = 1 := by
    have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) = Nat.gcd (14 * n + 3) (7 * n + 1) := by
      have h1 : 21 * n + 4 = (14 * n + 3) + (7 * n + 1) := by
        omega
      rw [h1]
      simp [Nat.gcd_add_self_left, Nat.gcd_comm]
    rw [h1]
    have h14 : Nat.gcd (14 * n + 3) (7 * n + 1) = 1 := by
      have h3 : 14 * n + 3 = 2 * (7 * n + 1) + 1 := by
        ring_nf
        <;> omega
      rw [h3]
      simp [Nat.gcd_add_self_left, Nat.gcd_comm, Nat.gcd_one_left, Nat.gcd_one_right]
      <;> try { omega }
    exact h14
  exact h2