import Mathlib

theorem algebra_13208 : Set.ncard {A : ℕ | A < 10 ∧ A ∣ 63 ∧ 4 ∣ Nat.ofDigits 10 [2, A, 1, 3, 7, 2]} = 4 := by
  have h1 : {A : ℕ | A < 10 ∧ A ∣ 63 ∧ 4 ∣ Nat.ofDigits 10 [2, A, 1, 3, 7, 2]} = {1, 3, 7, 9} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First: prove that all A that satisfy conditions must be in {1, 3, 7, 9}
      intro h
      rcases h with ⟨ha1, ha2, ha3⟩
      interval_cases A <;> norm_num [Nat.ofDigits] at ha3 ⊢ <;> tauto
    · -- Now prove that all A in {1, 3, 7, 9} satisfy the conditions
      rintro (rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        constructor
        · norm_num
        · -- Show 4 divides Nat.ofDigits 10 [2, 1, 1, 3, 7, 2]
          native_decide
      · constructor
        · norm_num
        constructor
        · norm_num
        · -- Show 4 divides Nat.ofDigits 10 [2, 3, 1, 3, 7, 2]
          native_decide
      · constructor
        · norm_num
        constructor
        · norm_num
        · -- Show 4 divides Nat.ofDigits 10 [2, 7, 1, 3, 7, 2]
          native_decide
      · constructor
        · norm_num
        constructor
        · norm_num
        · -- Show 4 divides Nat.ofDigits 10 [2, 9, 1, 3, 7, 2]
          native_decide
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }