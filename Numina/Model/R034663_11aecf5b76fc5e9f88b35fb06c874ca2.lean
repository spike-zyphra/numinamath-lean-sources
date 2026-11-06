import Mathlib

theorem number_theory_286062 (n : ℕ) :
    n % 3 = (Nat.digits 10 n).sum % 3 ∧ n % 9 = (Nat.digits 10 n).sum % 9 := by
  constructor
  · -- Prove that n % 3 = (Nat.digits 10 n).sum % 3
    have h3 : n % 3 = (Nat.digits 10 n).sum % 3 := by
      have h9 : n % 9 = (Nat.digits 10 n).sum % 9 := by
        rw [Nat.modEq_nine_digits_sum (n)]
      omega
    exact h3
  · -- Prove that n % 9 = (Nat.digits 10 n).sum % 9
    have h9 : n % 9 = (Nat.digits 10 n).sum % 9 := by
      rw [Nat.modEq_nine_digits_sum (n)]
    exact h9