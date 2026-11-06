import Mathlib

theorem number_theory_246496 (a m : ℕ) :
    9 ∣ (Nat.digits 10 (a ^ m)).sum - (Nat.digits 10 a).sum ^ m := by 
  have h1 : (Nat.digits 10 (a ^ m)).sum % 9 = (a ^ m) % 9 := by 
    rw [Nat.modEq_nine_digits_sum (a ^ m)]
    <;> omega
  have h2 : (Nat.digits 10 a).sum % 9 = a % 9 := by 
    rw [Nat.modEq_nine_digits_sum a]
    <;> omega
  have h3 : ((Nat.digits 10 (a ^ m)).sum) % 9 = ((Nat.digits 10 a).sum ^ m) % 9 := by
    have h4 : (a ^ m) % 9 = ( (Nat.digits 10 a).sum ^ m ) % 9 := by 
      have h5 : ( (Nat.digits 10 a).sum ) % 9 = a % 9 := by 
        rw [Nat.modEq_nine_digits_sum a]
        <;> omega
      have h6 : ( (Nat.digits 10 a).sum ^ m ) % 9 = ( a ^ m ) % 9 := by
        simp [Nat.pow_mod, h5]
        <;> omega
      omega
    omega
  exact Nat.dvd_of_mod_eq_zero (show ((Nat.digits 10 (a ^ m)).sum - (Nat.digits 10 a).sum ^ m) % 9 = 0 by 
    omega
  )