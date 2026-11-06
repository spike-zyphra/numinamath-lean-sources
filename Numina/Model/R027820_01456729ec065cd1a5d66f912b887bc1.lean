import Mathlib

theorem number_theory_6087 :
    Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ 20 ∧ ∃ a b, n = a ^ 2 + b ^ 2} = 12 := by
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 20 ∧ ∃ a b, n = a ^ 2 + b ^ 2} = 
          {1, 2, 4, 5, 8, 9, 10, 13, 16, 17, 18, 20} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First, show that if n is in the left side, it's in the right side
      rintro ⟨h1, h2, ⟨a, b, h3⟩⟩
      have h4 : a ≤ 4 := by nlinarith
      have h5 : b ≤ 4 := by nlinarith
      interval_cases a <;> interval_cases b <;> omega
    · -- Second, show that if n is in the right side, it's in the left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 1
        constructor
        · norm_num -- 1 >= 1
        constructor
        · norm_num -- 1 <= 20
        · -- exists a b, 1 = a^2 + b^2
          use 1, 0
          all_goals norm_num
      · -- n = 2
        constructor
        · norm_num -- 2 >= 1
        constructor
        · norm_num -- 2 <= 20
        · -- exists a b, 2 = a^2 + b^2
          use 1, 1
          all_goals norm_num
      · -- n = 4
        constructor
        · norm_num -- 4 >= 1
        constructor
        · norm_num -- 4 <= 20
        · -- exists a b, 4 = a^2 + b^2
          use 2, 0
          all_goals norm_num
      · -- n = 5
        constructor
        · norm_num -- 5 >= 1
        constructor
        · norm_num -- 5 <= 20
        · -- exists a b, 5 = a^2 + b^2
          use 2, 1
          all_goals norm_num
      · -- n = 8
        constructor
        · norm_num -- 8 >= 1
        constructor
        · norm_num -- 8 <= 20
        · -- exists a b, 8 = a^2 + b^2
          use 2, 2
          all_goals norm_num
      · -- n = 9
        constructor
        · norm_num -- 9 >= 1
        constructor
        · norm_num -- 9 <= 20
        · -- exists a b, 9 = a^2 + b^2
          use 3, 0
          all_goals norm_num
      · -- n = 10
        constructor
        · norm_num -- 10 >= 1
        constructor
        · norm_num -- 10 <= 20
        · -- exists a b, 10 = a^2 + b^2
          use 3, 1
          all_goals norm_num
      · -- n = 13
        constructor
        · norm_num -- 13 >= 1
        constructor
        · norm_num -- 13 <= 20
        · -- exists a b, 13 = a^2 + b^2
          use 3, 2
          all_goals norm_num
      · -- n = 16
        constructor
        · norm_num -- 16 >= 1
        constructor
        · norm_num -- 16 <= 20
        · -- exists a b, 16 = a^2 + b^2
          use 4, 0
          all_goals norm_num
      · -- n = 17
        constructor
        · norm_num -- 17 >= 1
        constructor
        · norm_num -- 17 <= 20
        · -- exists a b, 17 = a^2 + b^2
          use 4, 1
          all_goals norm_num
      · -- n = 18
        constructor
        · norm_num -- 18 >= 1
        constructor
        · norm_num -- 18 <= 20
        · -- exists a b, 18 = a^2 + b^2
          use 3, 3
          all_goals norm_num
      · -- n = 20
        constructor
        · norm_num -- 20 >= 1
        constructor
        · norm_num -- 20 <= 20
        · -- exists a b, 20 = a^2 + b^2
          use 4, 2
          all_goals norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }