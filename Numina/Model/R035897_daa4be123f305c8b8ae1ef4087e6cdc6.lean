import Mathlib

theorem number_theory_100628 (a : ℕ) (_ : a ≠ 0) (h : a < 2016)
    (h1 : Nat.Coprime a 2016) :
    Nat.Coprime 2016 (2016 - a) := by
  have h2 : Nat.Coprime 2016 a := by 
    exact Nat.coprime_comm.mp h1 
  have h3 : Nat.gcd 2016 (2016 - a) = 1 := by 
    have h4 : Nat.gcd 2016 (2016 - a) ∣ 2016 := by 
      apply Nat.gcd_dvd_left
    have h5 : Nat.gcd 2016 (2016 - a) ∣ (2016 - a : ℕ) := by 
      apply Nat.gcd_dvd_right 
    have h6 : Nat.gcd 2016 (2016 - a) ∣ a := by
      have h7 : Nat.gcd 2016 (2016 - a) ∣ (2016 : ℕ) := h4
      have h8 : Nat.gcd 2016 (2016 - a) ∣ (2016 - a : ℕ) := h5
      have h9 : Nat.gcd 2016 (2016 - a) ∣ ((2016 : ℕ) - (2016 - a) : ℕ) := by
        apply Nat.dvd_sub' 
        · exact h7 
        · exact h8 
      have h10 : (2016 : ℕ) - (2016 - a) = a := by 
        omega
      rw [h10] at h9
      exact h9
    have h9 : Nat.gcd 2016 (2016 - a) ∣ Nat.gcd 2016 a := by 
      apply Nat.dvd_gcd 
      · exact h4 
      · exact h6 
    have h10 : Nat.gcd 2016 a = 1 := by 
      rw [Nat.coprime_iff_gcd_eq_one] at h1
      have h11 : Nat.gcd a 2016 = 1 := h1
      have h12 : Nat.gcd 2016 a = Nat.gcd a 2016 := by 
        simp [Nat.gcd_comm]
      rw [h12] 
      exact h11
    rw [h10] at h9
    have h11 : Nat.gcd 2016 (2016 - a) ∣ 1 := h9 
    have h12 : Nat.gcd 2016 (2016 - a) = 1 := by
      exact Nat.dvd_one.mp h11
    exact h12
  rw [Nat.coprime_iff_gcd_eq_one] 
  exact h3