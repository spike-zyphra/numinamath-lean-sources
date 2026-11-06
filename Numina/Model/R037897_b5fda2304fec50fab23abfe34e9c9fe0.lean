import Mathlib

theorem number_theory_96736 (A B : ℕ) (hA : A ≠ 0) (abound:0≤A∧A≤9) (hB : B ≠ 0) (bbound:0≤B∧B≤9) :(Nat.digits 10 (Nat.ofDigits 10 [6,7,8,9]+ Nat.ofDigits 10 [2,3,A]+Nat.ofDigits 10 [1,B])).length = 5 := by

  have h1 : A ≥ 1 := by
    by_contra h
    push_neg at h
    have h2 : A = 0 := by 
      omega 
    contradiction

  have h2 : B ≥ 1 := by
    by_contra h
    push_neg at h
    have h3 : B = 0 := by 
      omega 
    contradiction

  have h3 : A ≤ 9 := abound.right
  have h4 : B ≤ 9 := bbound.right
  have h5 : (Nat.ofDigits 10 [6, 7, 8, 9] : ℕ) = 9876 := by 
    rfl 
  have h6 : (Nat.ofDigits 10 [2, 3, A] : ℕ) = 32 + 100 * A := by
    simp [Nat.ofDigits, Nat.add_mul, Nat.mul_add, mul_assoc]
    <;> ring_nf  
  have h7 : (Nat.ofDigits 10 [1, B] : ℕ) = 1 + 10 * B := by 
    simp [Nat.ofDigits, Nat.add_mul, Nat.mul_add, mul_assoc]
    <;> ring_nf  
  have h8 : (Nat.ofDigits 10 [6, 7, 8, 9] + Nat.ofDigits 10 [2, 3, A] + Nat.ofDigits 10 [1, B] : ℕ) = 9909 + 100 * A + 10 * B := by
    calc 
      (Nat.ofDigits 10 [6, 7, 8, 9] + Nat.ofDigits 10 [2, 3, A] + Nat.ofDigits 10 [1, B] : ℕ)
          = 9876 + (32 + 100 * A) + (1 + 10 * B) := by rw [h5, h6, h7]
      _ = 9876 + 32 + 1 + 100 * A + 10 * B := by ring
      _ = 9909 + 100 * A + 10 * B := by ring
  rw [h8]
  interval_cases A <;> interval_cases B <;> norm_num