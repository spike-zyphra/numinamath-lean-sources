import Mathlib

theorem number_theory_5942 :
    Set.ncard {n : ℕ | 0 < n ∧ n < 110 ∧ (Nat.digits 10 n).sum ≡ 0 [MOD 12]} = 7 := by 
  have h1 : {n : ℕ | 0 < n ∧ n < 110 ∧ (Nat.digits 10 n).sum ≡ 0 [MOD 12]} = 
          {39, 48, 57, 66, 75, 84, 93} := by 
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n ∈ {n : ℕ | 0 < n ∧ n < 110 ∧ (Nat.digits 10 n).sum ≡ 0 [MOD 12]}
      rintro ⟨h1, h2, h3⟩
      interval_cases n <;> norm_num [Nat.ModEq] at h3 ⊢
      <;> tauto
    · -- Assume n ∈ {39, 48, 57, 66, 75, 84, 93}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        constructor
        · norm_num 
        constructor
        · norm_num
        · norm_num [Nat.ModEq]
  rw [h1]
  norm_num