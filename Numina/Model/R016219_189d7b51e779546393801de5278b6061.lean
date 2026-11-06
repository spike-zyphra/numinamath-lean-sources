import Mathlib

theorem number_theory_113457 (n : ℕ) :
    Nat.Coprime (n^5 + 4 * n^3 + 3 * n) (n^4 + 3 * n^2 + 1) := by
  have h1 : Nat.gcd (n^5 + 4 * n^3 + 3 * n) (n^4 + 3 * n^2 + 1) = 1 := by
    have h2 : Nat.gcd (n^5 + 4 * n^3 + 3 * n) (n^4 + 3 * n^2 + 1) =
        Nat.gcd (n^4 + 3 * n^2 + 1) (n^3 + 2 * n) := by
      simp [Nat.gcd_comm, show n ^ 5 + 4 * n ^ 3 + 3 * n = n * (n ^ 4 + 3 * n ^ 2 + 1) + (n^3 + 2 * n) by ring]
    have h3 : Nat.gcd (n^4 + 3 * n^2 + 1) (n^3 + 2 * n) =
        Nat.gcd (n^3 + 2 * n) (n^2 + 1) := by
      simp [Nat.gcd_comm, show n ^ 4 + 3 * n ^ 2 + 1 = n * (n ^ 3 + 2 * n) + (n ^ 2 + 1) by ring]
    have h4 : Nat.gcd (n^3 + 2 * n) (n^2 + 1) =
        Nat.gcd (n^2 + 1) (n) := by
      simp [Nat.gcd_comm, show n ^ 3 + 2 * n = n * (n ^ 2 + 1) + n by ring]
    have h5 : Nat.gcd (n^2 + 1) (n) = 1 := by
      have h7 : Nat.gcd (n^2 + 1) (n) ∣ (n^2 + 1) := by 
        apply Nat.gcd_dvd_left
      have h8 : Nat.gcd (n^2 + 1) (n) ∣ (n) := by 
        apply Nat.gcd_dvd_right
      have h9 : Nat.gcd (n^2 + 1) (n) ∣ ((n^2 + 1) - n * n) := by
        apply Nat.dvd_sub'
        · -- Show that gcd (n^2 + 1) n divides n^2 + 1
          exact h7
        · -- Show that gcd (n^2 + 1) n divides n * n
          have h10 : Nat.gcd (n^2 + 1) (n) ∣ (n * n) := by
            apply Dvd.dvd.mul_right
            exact h8
          exact h10
      have h10 : ((n^2 + 1) - n * n) = 1 := by 
        cases n with
        | zero => 
          simp
        | succ m => 
          simp [Nat.pow_succ, Nat.mul_add]
          <;> ring_nf
          <;> omega
      have h11 : Nat.gcd (n^2 + 1) (n) ∣ 1 := by 
        rw [h10] at h9
        exact h9
      have h12 : Nat.gcd (n^2 + 1) (n) = 1 := by 
        exact Nat.eq_one_of_dvd_one h11
      exact h12
    rw [h2, h3, h4, h5]
  rw [Nat.coprime_iff_gcd_eq_one]
  exact h1