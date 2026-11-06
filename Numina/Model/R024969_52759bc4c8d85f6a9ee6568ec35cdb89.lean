import Mathlib

theorem number_theory_251895 (n : ℕ) :
    9 ∣ n ↔ ∃ k, k = (Nat.digits 10 n).sum ∧ 9 ∣ k := by
  constructor
  · -- Forward direction: if 9 divides n, then the sum of its digits is divisible by 9
    intro h
    refine' ⟨(Nat.digits 10 n).sum, rfl, by
      have h1 : n % 9 = 0 := by 
        omega
      have h3 : (Nat.digits 10 n).sum % 9 = 0 := by
        have h4 : n % 9 = (Nat.digits 10 n).sum % 9 := by 
          rw [Nat.modEq_nine_digits_sum (n)]
        omega
      omega⟩
  · -- Backward direction: if the sum of the digits is divisible by 9, then n is divisible by 9
    rintro ⟨k, hk, hk9⟩
    have h3 : k % 9 = 0 := by 
      omega 
    have h4 : n % 9 = 0 := by 
      have h5 : k = (Nat.digits 10 n).sum := by 
        omega 
      have h6 : (Nat.digits 10 n).sum % 9 = 0 := by 
        omega 
      have h7 : n % 9 = (Nat.digits 10 n).sum % 9 := by 
        rw [Nat.modEq_nine_digits_sum (n)]
      omega 
    omega