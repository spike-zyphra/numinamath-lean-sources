import Mathlib

theorem number_theory_83268 (x : ℕ) (h : (Nat.digits 10 x).sum = (Nat.digits 10 (3 * x)).sum) :
  9 ∣ x := by
  have h1 : x % 9 = (Nat.digits 10 x).sum % 9 := by 
    rw [Nat.modEq_nine_digits_sum]
  
  have h2 : (3 * x) % 9 = (Nat.digits 10 (3 * x)).sum % 9 := by
    rw [Nat.modEq_nine_digits_sum]

  have h3 : x % 9 = (3 * x) % 9 := by
    have h4 : (Nat.digits 10 x).sum % 9 = (Nat.digits 10 (3 * x)).sum % 9 := by 
      omega -- Given h: (Nat.digits 10 x).sum = (Nat.digits 10 (3 * x)).sum, so their mod 9's are equal
    rw [show (Nat.digits 10 x).sum % 9 = x % 9 by omega] at h4
    rw [show (Nat.digits 10 (3 * x)).sum % 9 = (3 * x) % 9 by omega] at h4
    omega
  
  have h4 : x % 9 = 0 := by
    omega
  
  exact Nat.dvd_of_mod_eq_zero h4