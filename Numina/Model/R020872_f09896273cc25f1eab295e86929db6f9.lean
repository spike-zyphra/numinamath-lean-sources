import Mathlib

theorem number_theory_122754 (n : ℕ) :
    (n % 3 = 0 ↔ (Nat.digits 10 n).sum ≡ 0 [MOD 3]) ∧
    (n % 9 = 0 ↔ (Nat.digits 10 n).sum ≡ 0 [MOD 9]) := by
  constructor
  · -- Show that a number is divisible by 3 if and only if the sum of its digits is a multiple of 3
    apply Iff.intro
    · -- Assume n % 3 = 0, prove (Nat.digits 10 n).sum ≡ 0 [MOD 3]
      intro h
      have h1 : n % 3 = (Nat.digits 10 n).sum % 3 := by
        have h2 : n % 9 = (Nat.digits 10 n).sum % 9 := by
          rw [Nat.modEq_nine_digits_sum (n)]
        have h3 : n % 3 = (n % 9) % 3 := by 
          omega
        have h4 : ((Nat.digits 10 n).sum % 9) % 3 = (Nat.digits 10 n).sum % 3 := by 
          omega
        have h5 : n % 9 % 3 = ((Nat.digits 10 n).sum % 9) % 3 := by 
          omega
        omega
      have h2 : (Nat.digits 10 n).sum % 3 = 0 := by 
        omega
      simp [Nat.ModEq] at *
      omega
    · -- Assume (Nat.digits 10 n).sum ≡ 0 [MOD 3], prove n % 3 = 0
      intro h 
      have h1 : n % 3 = (Nat.digits 10 n).sum % 3 := by 
        have h2 : n % 9 = (Nat.digits 10 n).sum % 9 := by 
          rw [Nat.modEq_nine_digits_sum (n)]
        have h3 : n % 3 = (n % 9) % 3 := by 
          omega 
        have h4 : ((Nat.digits 10 n).sum % 9) % 3 = (Nat.digits 10 n).sum % 3 := by 
          omega 
        have h5 : n % 9 % 3 = ((Nat.digits 10 n).sum % 9) % 3 := by 
          omega 
        omega 
      have h2 : (Nat.digits 10 n).sum % 3 = 0 := by 
        simp [Nat.ModEq] at h 
        omega 
      omega 
  · -- Show that a number is divisible by 9 if and only if the sum of its digits is a multiple of 9 
    apply Iff.intro 
    · -- Assume n % 9 = 0, prove (Nat.digits 10 n).sum ≡ 0 [MOD 9] 
      intro h 
      have h1 : n % 9 = (Nat.digits 10 n).sum % 9 := by 
        rw [Nat.modEq_nine_digits_sum (n)]
      have h2 : (Nat.digits 10 n).sum % 9 = 0 := by 
        omega 
      simp [Nat.ModEq] at *
      omega 
    · -- Assume (Nat.digits 10 n).sum ≡ 0 [MOD 9], prove n % 9 = 0 
      intro h 
      have h1 : n % 9 = (Nat.digits 10 n).sum % 9 := by 
        rw [Nat.modEq_nine_digits_sum (n)]
      have h2 : (Nat.digits 10 n).sum % 9 = 0 := by 
        simp [Nat.ModEq] at h 
        omega 
      omega