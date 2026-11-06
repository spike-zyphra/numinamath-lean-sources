import Mathlib

theorem number_theory_78796 :
    Set.ncard {n : ℕ | 10 < n ∧ n < 100 ∧ (Nat.digits 10 n).length = 2 ∧
      n + 9 = (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n)))} = 8 := by
  have h1 : {n : ℕ | 10 < n ∧ n < 100 ∧ (Nat.digits 10 n).length = 2 ∧
    n + 9 = (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n)))} = {12, 23, 34, 45, 56, 67, 78, 89} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Forward direction: if n is in the set then it is in {12, 23, 34, 45, 56, 67, 78, 89}
      rintro ⟨h1, h2, h3, h4⟩
      interval_cases n <;> norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux] at h4 ⊢ <;> omega
    · -- Backward direction: if n is in {12, 23, 34, 45, 56, 67, 78, 89} then it is in the set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify for 12
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify for 23
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify for 34
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify for 45
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify for 56
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify for 67
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify for 78
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Verify for 89
          norm_num [Nat.ofDigits, Nat.digits, Nat.digitsAux]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try native_decide