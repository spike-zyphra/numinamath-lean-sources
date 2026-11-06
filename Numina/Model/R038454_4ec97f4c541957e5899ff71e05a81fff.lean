import Mathlib

theorem number_theory_276146 {a b : ℕ} (ha : a < b) (hb : b ≠ 0) :
    Nat.Coprime a b → Nat.Coprime (b - a) b := by
  intro h
  have h1 : Nat.gcd (b - a) b ∣ a := by 
    have h3 : Nat.gcd (b - a) b ∣ b := by 
      apply Nat.gcd_dvd_right 
    have h4 : Nat.gcd (b - a) b ∣ (b - a) := by 
      apply Nat.gcd_dvd_left 
    have h5 : Nat.gcd (b - a) b ∣ b - (b - a) := by 
      apply Nat.dvd_sub' 
      · exact h3 
      · exact h4 
    have h7 : b - (b - a) = a := by 
      omega 
    rw [h7] at h5 
    exact h5 
  have h8 : Nat.gcd (b - a) b ∣ Nat.gcd a b := by 
    apply Nat.dvd_gcd 
    · exact h1 
    · exact Nat.gcd_dvd_right (b - a) b 
  have h9 : Nat.gcd a b = 1 := by 
    rw [Nat.coprime_iff_gcd_eq_one] at h 
    exact h 
  have h10 : Nat.gcd (b - a) b ∣ 1 := by 
    rw [h9] at h8 
    exact h8 
  have h11 : Nat.gcd (b - a) b = 1 := by 
    have h12 : Nat.gcd (b - a) b ∣ 1 := h10
    have h13 : Nat.gcd (b - a) b > 0 := by 
      apply Nat.gcd_pos_of_pos_right 
      all_goals 
        omega 
    have h14 : Nat.gcd (b - a) b ≤ 1 := by 
      exact Nat.le_of_dvd (by linarith) h12 
    interval_cases (Nat.gcd (b - a) b) <;> try { omega } 
  rw [Nat.coprime_iff_gcd_eq_one] 
  exact h11