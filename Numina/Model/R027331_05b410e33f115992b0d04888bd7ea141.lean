import Mathlib

theorem number_theory_281049 :
    IsGreatest {x | ∃ m n : ℕ, x = Nat.gcd (m + 2000 * n) (n + 2000 * m) ∧ Nat.gcd m n = 1} (2000 ^ 2 - 1) := by 
  constructor 
  · -- Show that 2000^2 - 1 is in the set. 
    use 3997999, 1
    all_goals 
      norm_num [Nat.gcd]
  · -- Show that 2000^2 - 1 is greatest
    intro x hx 
    rcases hx with ⟨m, n, hx_eq, h1⟩
    have h2 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (m + 2000 * n) := by 
      apply Nat.gcd_dvd_left 
    have h3 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (n + 2000 * m) := by 
      apply Nat.gcd_dvd_right 
    have h8 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (2000 ^ 2 - 1) * n := by 
      have h9 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (2000 * (m + 2000 * n) - (n + 2000 * m)) := by
        apply Nat.dvd_sub' 
        · -- Show that 2000 * (m + 2000 * n) is divisible by the GCD 
          have h10 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (2000 * (m + 2000 * n)) := by 
            apply dvd_trans (show Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (m + 2000 * n) by apply Nat.gcd_dvd_left) 
            simp [Nat.pow_succ, Nat.mul_assoc]
          exact h10 
        · --  Show that n + 2000 * m is divisible by the GCD 
          apply h3 
      have h11 : 2000 * (m + 2000 * n) - (n + 2000 * m) = (2000 ^ 2 - 1) * n := by 
        omega 
      rw [h11] at h9 
      exact h9 
    have h9 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (2000 ^ 2 - 1) * m := by 
      have h10 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (2000 * (n + 2000 * m) - (m + 2000 * n)) := by
        apply Nat.dvd_sub' 
        · -- Show that 2000 * (n + 2000 * m) is divisible by the GCD 
          have h11 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (2000 * (n + 2000 * m)) := by 
            apply dvd_trans (show Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (n + 2000 * m) by apply Nat.gcd_dvd_right) 
            simp [Nat.pow_succ, Nat.mul_assoc]
          exact h11 
        · -- Show that m + 2000 * n is divisible by the GCD 
          apply h2 
      have h12 : 2000 * (n + 2000 * m) - (m + 2000 * n) = (2000 ^ 2 - 1) * m := by 
        omega 
      rw [h12] at h10 
      exact h10 
    have h5c : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (2000 ^ 2 - 1) := by 
      have h6 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (2000 ^ 2 - 1) * n := h8 
      have h7 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (2000 ^ 2 - 1) * m := h9 
      have h8 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ Nat.gcd ((2000 ^ 2 - 1) * n) ((2000 ^ 2 - 1) * m) := by 
        apply Nat.dvd_gcd 
        exact h6 
        exact h7 
      have h9 : Nat.gcd ((2000 ^ 2 - 1) * n) ((2000 ^ 2 - 1) * m) = (2000 ^ 2 - 1) * Nat.gcd n m := by 
        rw [Nat.gcd_mul_left] 
      rw [h9] at h8 
      have h5 : Nat.gcd n m = 1 := by 
        have h5 : Nat.gcd m n = 1 := h1 
        have h6 : Nat.gcd n m = Nat.gcd m n := by 
          simp [Nat.gcd_comm]
        rw [h6] at *
        exact h5 
      rw [h5] at h8 
      exact h8 
    have h12 : x ∣ (2000 ^ 2 - 1) := by 
      rw [hx_eq] at *
      exact h5c 
    have h13 : x ≤ (2000 ^ 2 - 1) := by 
      exact Nat.le_of_dvd (by norm_num) h12 
    linarith