import Mathlib

theorem algebra_20538 : IsLeast {N : ℕ | 12 ∣ N ∧ ∃ A B : ℕ, A ≠ 0 ∧ B ≠ 0 ∧ Nat.digits 10 N = [B, A, 9, 4, 1]} 14916 := by
  constructor
  · -- Show that 14916 is in the set.
    constructor
    · -- Show 14916 is divisible by 12.
      norm_num
    · -- Show the existence of A, B.
      use 1, 6
      all_goals norm_num
  · -- Show that 14916 is the smallest
    intro N ⟨h1, ⟨A, B, hA, hB, h2⟩⟩ 
    by_contra h
    push_neg at h 
    have h4 : A ≥ 1 := by 
      omega
    have h5 : B ≥ 1 := by 
      omega 
    have h6 : N ≥ 14900 := by 
      have h7 : Nat.digits 10 N = [B, A, 9, 4, 1] := h2 
      have h8 : N = 1 * 10000 + 4 * 1000 + 9 * 100 + A * 10 + B := by
        rw [← Nat.ofDigits_digits 10 N]
        rw [h7]
        simp [Nat.ofDigits, Nat.add_assoc, Nat.mul_add, mul_assoc]
        all_goals omega 
      omega 
    have h7 : N < 14916 := by linarith 
    have h8 : N ≤ 14915 := by 
      omega 
    interval_cases N <;> simp_all [Nat.ofDigits, Nat.digits, Nat.digitsAux] <;> try { 
      omega 
    }