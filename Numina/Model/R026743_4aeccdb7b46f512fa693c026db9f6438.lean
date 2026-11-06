import Mathlib

theorem number_theory_323515 (n : ℕ) :
    Nat.Coprime (21*n+4) (14*n+3) := by
  have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
    have eq4 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 1 := by
      have h3 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (21 * n + 4 : ℕ) := by
        apply Nat.gcd_dvd_left
      have h4 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (14 * n + 3 : ℕ) := by
        apply Nat.gcd_dvd_right
      have h5 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (3 * (14 * n + 3) : ℕ) := by
        apply dvd_trans h4 
        simp
      have h6 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (2 * (21 * n + 4) : ℕ) := by
        apply dvd_trans h3 
        simp
      have h7 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (3 * (14 * n + 3) - 2 * (21 * n + 4) : ℕ) := by
        apply Nat.dvd_sub' 
        · -- Show that gcd divides 3*(14*n+3)
          exact h5
        · -- Show that gcd divides 2*(21*n+4)
          exact h6
      have h8 : (3 * (14 * n + 3) - 2 * (21 * n + 4) : ℕ) = 1 := by 
        omega
      rw [h8] at h7
      exact_mod_cast h7
    have h9 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 1 := by
      exact_mod_cast eq4
    have h10 : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
      exact Nat.eq_one_of_dvd_one h9 
    exact_mod_cast h10
  rw [Nat.coprime_iff_gcd_eq_one] 
  exact_mod_cast h1