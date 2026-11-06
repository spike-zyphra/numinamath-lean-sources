import Mathlib

theorem number_theory_209021 :
  { n : ℕ | n > 0 ∧ n % 45 = 0 ∧
    ∃ a b c : ℕ,
      Nat.digits 10 n = [a, b, c] ∧
      a + c = 2 * b
  }
  =
  {135, 630, 765} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Proof of the → direction: if n is in the left side, it must be in the right side.
    rintro ⟨hn_pos, hn_mod, ⟨a, b, c, h1, h2⟩⟩
    have h3 : n % 45 = 0 := hn_mod
    have h4 : n > 0 := hn_pos
    have h5 : n = a + b * 10 + c * 100 := by
      have h6 : Nat.digits 10 n = [a, b, c] := h1
      have eq1 : n = Nat.ofDigits 10 (Nat.digits 10 n) := by
        rw [Nat.ofDigits_digits]
      rw [h6] at eq1
      simp [Nat.ofDigits, mul_add, add_mul] at eq1 ⊢
      omega
    -- Commute to Lean 4 element, and by element in congr range can solve
    have h6 : a ≤ 9 := by
      have h7 : a < 10 := by 
        have h8 : a ∈ Nat.digits 10 n := by
          simp [h1]
        have h9 : a < 10 := by
          exact Nat.digits_lt_base (by norm_num) h8
        omega
      omega
    have h7 : b ≤ 9 := by
      have h8 : b < 10 := by 
        have h9 : b ∈ Nat.digits 10 n := by
          simp [h1]
        have h10 : b < 10 := by
          exact Nat.digits_lt_base (by norm_num) h9
        omega
      omega
    have h8 : c ≤ 9 := by
      have h9 : c < 10 := by 
        have h10 : c ∈ Nat.digits 10 n := by
          simp [h1]
        have h11 : c < 10 := by
          exact Nat.digits_lt_base (by norm_num) h10
        omega
      omega
    -- bounded digits to finite sets, which Lean 4 can decide
    interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num [h5] at h3 h4 h2 ⊢  <;> tauto
  · -- Proof of the ← direction: if n is in the right side, it must be in the left side.
    rintro (rfl | rfl | rfl)
    · -- n = 135
      constructor 
      · norm_num
      constructor
      · norm_num
      · -- Show existence of a, b, c
        use 5, 3, 1
        all_goals 
          norm_num
    · -- n = 630
      constructor 
      · norm_num
      constructor
      · norm_num
      · -- Show existence of a, b, c
        use 0, 3, 6
        all_goals 
          norm_num
    · -- n = 765
      constructor 
      · norm_num
      constructor
      · norm_num
      · -- Show existence of a, b, c
        use 5, 6, 7
        all_goals 
          norm_num