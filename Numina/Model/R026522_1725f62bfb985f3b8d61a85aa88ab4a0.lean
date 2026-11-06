import Mathlib

theorem number_theory_309696 (n : ℕ) (hn : n > 0) :
    Nat.Coprime (3 * n + 1) (5 * n + 2) := by 
  show Nat.Coprime (3 * n + 1) (5 * n + 2)
  have h1 : Nat.gcd (3 * n + 1) (5 * n + 2) = 1 := by
    have h11 : Nat.gcd (3 * n + 1) (5 * n + 2) ∣ (3 * n + 1) := by
      exact Nat.gcd_dvd_left (3 * n + 1) (5 * n + 2)
    have h12 : Nat.gcd (3 * n + 1) (5 * n + 2) ∣ (5 * n + 2) := by
      exact Nat.gcd_dvd_right (3 * n + 1) (5 * n + 2)
    have h13 : Nat.gcd (3 * n + 1) (5 * n + 2) ∣ 1 := by
      have h2 : Nat.gcd (3 * n + 1) (5 * n + 2) ∣ (3 * (5 * n + 2) - 5 * (3 * n + 1)) := by
        apply Nat.dvd_sub'
        · -- Show Nat.gcd (3 * n + 1) (5 * n + 2) divides 3 * (5 * n + 2)
          apply Nat.dvd_trans h12
          simp
        · -- Show Nat.gcd (3 * n + 1) (5 * n + 2) divides 5 * (3 * n + 1)
          apply Nat.dvd_trans h11
          simp
      have h14 : (3 * (5 * n + 2) - 5 * (3 * n + 1)) = 1 := by
        omega
      rw [h14] at h2
      exact h2
    have h14 : Nat.gcd (3 * n + 1) (5 * n + 2) = 1 := by 
      exact Nat.dvd_one.mp h13
    exact h14
  rw [Nat.coprime_iff_gcd_eq_one]
  exact h1