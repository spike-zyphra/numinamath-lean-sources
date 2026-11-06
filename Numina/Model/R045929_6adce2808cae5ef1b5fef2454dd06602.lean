import Mathlib

theorem number_theory_14891 : {n : ℕ | n > 0 ∧ ∃ A B : ℕ, Nat.digits 7 n = [B, A] ∧ Nat.digits 5 n = [A, B]} = {17} := by 
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n in the set, so prove n = 17
    intro h
    rcases h with ⟨hn_pos, ⟨A, B, h7, h5⟩⟩
    have h1 : n = 7 * A + B := by
      rw [← Nat.ofDigits_digits 7 n]
      rw [h7]
      simp [Nat.ofDigits, mul_add, mul_one]
      <;> omega
    have h2 : n = 5 * B + A := by
      rw [← Nat.ofDigits_digits 5 n]
      rw [h5]
      simp [Nat.ofDigits, mul_add, mul_one]
      <;> omega
    have h3 : 3 * A = 2 * B := by
      omega
    have hA5 : A < 5 := by 
      have h7 : Nat.digits 5 n = [A, B] := h5
      have hA : A ∈ Nat.digits 5 n := by 
        simp [h7]
      have hA5 : A < 5 := by
        exact Nat.digits_lt_base (by norm_num) hA
      omega
    have hB5 : B < 5 := by 
      have h7 : Nat.digits 5 n = [A, B] := h5
      have hB : B ∈ Nat.digits 5 n := by
        simp [h7]
      have hB5 : B < 5 := by
        exact Nat.digits_lt_base (by norm_num) hB
      omega
    have hA2 : A = 2 := by 
      omega
    have hB3 : B = 3 := by
      omega
    omega
  · -- Assume n = 17, prove in the set
    intro h
    rw [h]
    constructor
    · norm_num
    · -- Show existence of A and B
      use 2, 3
      all_goals 
        native_decide