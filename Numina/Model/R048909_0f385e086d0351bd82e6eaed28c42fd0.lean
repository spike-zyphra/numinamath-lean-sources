import Mathlib

theorem number_theory_106638 (n : ℕ) : 9 ∣ n - (Nat.digits 10 n).sum := by 
  apply Nat.dvd_of_mod_eq_zero
  have h1 : n % 9 = (Nat.digits 10 n).sum % 9 := by 
    rw [Nat.modEq_nine_digits_sum (n)]
  omega