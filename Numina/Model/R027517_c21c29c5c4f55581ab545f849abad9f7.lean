import Mathlib

theorem number_theory_127937 (n : ℕ) (h : (Nat.digits 10 n).sum = (Nat.digits 10 (3 * n)).sum) :
    9 ∣ n := by 
  have h1 : n % 9 = (Nat.digits 10 n).sum % 9 := by 
    rw [Nat.modEq_nine_digits_sum (n)]
  have h2 : (3 * n) % 9 = (Nat.digits 10 (3 * n)).sum % 9 := by 
    rw [Nat.modEq_nine_digits_sum (3 * n)]
  have h3 : n % 9 = (3 * n) % 9 := by 
    have h4 : (Nat.digits 10 n).sum % 9 = (Nat.digits 10 (3 * n)).sum % 9 := by 
      omega 
    omega 
  have h4 : n % 9 = 0 := by 
    omega 
  exact Nat.dvd_of_mod_eq_zero h4