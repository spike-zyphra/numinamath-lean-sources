import Mathlib

theorem number_theory_147806 (n : ℕ) :
    Nat.Coprime (21*n + 4) (14*n + 3) := by 
  have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
    have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (21 * n + 4 : ℕ) := by
      apply Nat.gcd_dvd_left
    have h2 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (14 * n + 3 : ℕ) := by
      apply Nat.gcd_dvd_right
    have h3 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (3 * (14 * n + 3) : ℕ) := by
      exact dvd_trans h2 (by simp)
    have h4 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (2 * (21 * n + 4) : ℕ) := by
      exact dvd_trans h1 (by simp)
    have h5 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (3 * (14 * n + 3) - 2 * (21 * n + 4) : ℕ) := by 
      apply Nat.dvd_sub' 
      · -- Show that Nat.gcd (21 * n + 4) (14 * n + 3) divides 3*(14n+3)
        exact h3 
      · -- Show that Nat.gcd (21 * n + 4) (14 * n + 3) divides 2*(21n+4)
        exact h4 
    have h6 : (3 * (14 * n + 3) - 2 * (21 * n + 4) : ℕ) = 1 := by 
      omega 
    rw [h6] at h5 
    have h7 : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by 
      exact Nat.eq_one_of_dvd_one h5 
    exact h7
  rw [Nat.coprime_iff_gcd_eq_one] 
  exact h1