import Mathlib

theorem number_theory_230982 :
    {n : ℕ | n ∈ Finset.Icc 100 999 ∧ n = (Nat.digits 10 n).headI + (Nat.digits 10 n).tail.headI + (Nat.digits 10 n).tail.tail.headI + (Nat.digits 10 n).headI * (Nat.digits 10 n).tail.headI + (Nat.digits 10 n).tail.headI * (Nat.digits 10 n).tail.tail.headI + (Nat.digits 10 n).headI * (Nat.digits 10 n).tail.tail.headI + (Nat.digits 10 n).headI * (Nat.digits 10 n).tail.headI * (Nat.digits 10 n).tail.tail.headI} =
    {199, 299, 399, 499, 599, 699, 799, 899, 999} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume n in LHS, prove n in RHS
    intro h
    rcases h with ⟨⟨hn1, hn2⟩, hneq⟩
    interval_cases n <;> norm_num at hneq hn1 hn2 ⊢ <;> omega
  · -- Assume n in RHS, prove n in LHS
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- n = 199
      constructor
      · -- Show n is three-digit
        norm_num
      · -- Show n = expression
        norm_num
    · -- n = 299
      constructor
      · -- Show n is three-digit
        norm_num
      · -- Show n = expression
        norm_num
    · -- n = 399
      constructor
      · -- Show n is three-digit
        norm_num
      · -- Show n = expression
        norm_num
    · -- n = 499
      constructor
      · -- Show n is three-digit
        norm_num
      · -- Show n = expression
        norm_num
    · -- n = 599
      constructor
      · -- Show n is three-digit
        norm_num
      · -- Show n = expression
        norm_num
    · -- n = 699
      constructor
      · -- Show n is three-digit
        norm_num
      · -- Show n = expression
        norm_num
    · -- n = 799
      constructor
      · -- Show n is three-digit
        norm_num
      · -- Show n = expression
        norm_num
    · -- n = 899
      constructor
      · -- Show n is three-digit
        norm_num
      · -- Show n = expression
        norm_num
    · -- n = 999
      constructor
      · -- Show n is three-digit
        norm_num
      · -- Show n = expression
        norm_num