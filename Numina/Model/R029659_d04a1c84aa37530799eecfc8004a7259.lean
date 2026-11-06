import Mathlib
theorem algebra_611144 (F : ℕ → ℕ) (h0 : F 0 = 0) (h1 : F 1 = 1) (h : ∀ n : ℕ, F (n + 2) = F (n + 1) + F n) : {n : ℕ | n ≤ 100 ∧ F n ≡ 0 [ZMOD 13]}.ncard = 15:= by

  have h2 : {n : ℕ | n ≤ 100 ∧ F n ≡ 0 [ZMOD 13]} = {0, 7, 14, 21, 28, 35, 42, 49, 56, 63, 70, 77, 84, 91, 98} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First direction: n ≤ 100 ∧ F n ≡ 0 [ZMOD 13] implies n ∈ {0, 7, 14, ..., 98}
      intro h
      rcases h with ⟨hn1, hn2⟩
      interval_cases n <;> norm_num [Int.ModEq, h0, h1, h] at hn2 ⊢
      <;> omega
    · -- Second direction: n ∈ {0, 7, 14, ..., 98} implies n ≤ 100 ∧ F n ≡ 0 [ZMOD 13]
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 0
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0]
      · -- n = 7
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
      · -- n = 14
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
      · -- n = 21
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
      · -- n = 28
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
      · -- n = 35
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
      · -- n = 42
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
      · -- n = 49
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
      · -- n = 56
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
      · -- n = 63
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
      · -- n = 70
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
      · -- n = 77
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
      · -- n = 84
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
      · -- n = 91
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
      · -- n = 98
        constructor
        · norm_num
        · norm_num [Int.ModEq, h0, h1, h]
  rw [h2]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }