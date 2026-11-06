import Mathlib

theorem number_theory_136850 (n : ℕ) :
    Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  have h1 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (21 * n + 4) := by
    apply Nat.gcd_dvd_left
  have h2 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (14 * n + 3) := by
    apply Nat.gcd_dvd_right
  have h3 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ 1 := by
    have h4 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (3 * (14 * n + 3) : ℕ) := by
      apply dvd_trans h2
      simp
    have h5 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣ (2 * (21 * n + 4) : ℕ) := by
      apply dvd_trans h1
      simp
    have h6 : Nat.gcd (21 * n + 4) (14 * n + 3) ∣
      (3 * (14 * n + 3) - 2 * (21 * n + 4) : ℕ) := by
      apply Nat.dvd_sub'
      · -- Show that Nat.gcd (21 * n + 4) (14 * n + 3) divides 3 * (14 * n + 3)
        exact h4
      · -- Show that Nat.gcd (21 * n + 4) (14 * n + 3) divides 2 * (21 * n + 4)
        exact h5
    have h7 : (3 * (14 * n + 3) - 2 * (21 * n + 4) : ℕ) = 1 := by
      omega
    rw [h7] at h6
    exact h6
  exact Nat.eq_one_of_dvd_one h3