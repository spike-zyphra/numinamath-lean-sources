import Mathlib

theorem number_theory_5781
    (m a b : ℕ) (hcoprime : Nat.Coprime m a) :
    Nat.gcd m (a * b) = Nat.gcd m b := by 
  have h2 : Nat.gcd m (a * b) ∣ m := by 
    apply Nat.gcd_dvd_left
  have h3 : Nat.gcd m (a * b) ∣ (a * b) := by 
    apply Nat.gcd_dvd_right
  -- Prove that $\gcd(m, ab)$ is coprime to $a$.
  have h12 : Nat.Coprime (Nat.gcd m (a * b)) a := by
    have h13 : Nat.gcd (Nat.gcd m (a * b)) a = 1 := by 
      have h14 : Nat.gcd (Nat.gcd m (a * b)) a ∣ Nat.gcd m (a * b) := by 
        apply Nat.gcd_dvd_left
      have h15 : Nat.gcd (Nat.gcd m (a * b)) a ∣ a := by 
        apply Nat.gcd_dvd_right
      have h16 : Nat.gcd (Nat.gcd m (a * b)) a ∣ m := by 
        exact Nat.dvd_trans h14 (by 
          apply Nat.gcd_dvd_left
        )
      have h17 : Nat.gcd (Nat.gcd m (a * b)) a ∣ Nat.gcd m a := by 
        apply Nat.dvd_gcd
        . exact h16 
        . exact h15
      have h18 : Nat.gcd m a = 1 := by 
        rw [Nat.coprime_iff_gcd_eq_one] at hcoprime
        exact hcoprime
      rw [h18] at h17 
      have h18 : Nat.gcd (Nat.gcd m (a * b)) a = 1 := by 
        exact Nat.dvd_antisymm (by 
          exact h17
        ) (by 
          simp
        )
      exact h18 
    rw [Nat.coprime_iff_gcd_eq_one] 
    exact h13 
  -- Prove that $\gcd(m, ab) \mid b$.
  have h4 : Nat.gcd m (a * b) ∣ b := by 
    have h14 : Nat.Coprime (Nat.gcd m (a * b)) a := h12
    have h15 : Nat.gcd m (a * b) ∣ (a * b) := by 
      apply Nat.gcd_dvd_right 
    -- From the coprime condition, derive divisibility of b
    have h16 : Nat.gcd m (a * b) ∣ b := by 
      apply (Nat.Coprime.dvd_of_dvd_mul_left h14) h15 
    exact h16 
  have h6 : Nat.gcd m (a * b) ∣ Nat.gcd m b := by 
    apply Nat.dvd_gcd 
    . exact h2 
    . exact h4 
  -- Prove the reverse divisibility.
  have h7 : Nat.gcd m b ∣ Nat.gcd m (a * b) := by 
    apply Nat.dvd_gcd 
    . -- Show that `gcd m b` divides `m`
      apply Nat.gcd_dvd_left 
    . -- Show that `gcd m b` divides `a * b`
      have h8 : Nat.gcd m b ∣ b := by 
        apply Nat.gcd_dvd_right 
      have h9 : Nat.gcd m b ∣ (a * b) := by 
        apply dvd_trans h8 
        simp 
      exact h9 
  -- Since they divide each other, they must be equal.
  have h8 : Nat.gcd m (a * b) = Nat.gcd m b := by 
    apply Nat.dvd_antisymm 
    . exact h6 
    . exact h7 
  exact h8