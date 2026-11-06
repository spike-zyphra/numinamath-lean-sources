import Mathlib

theorem algebra_210057 :
    Set.ncard {k : ℤ | 1000 < k ∧ k < 2020 ∧ ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = k} = 13 := by 
  have h1 : {k : ℤ | 1000 < k ∧ k < 2020 ∧ ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = k} = 
  {1065, 1139, 1213, 1287, 1361, 1435, 1509, 1583, 1657, 1731, 1805, 1879, 1953} := by 
    ext k 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume k is in the left side, so assume the conjunction of conditions
      rintro ⟨hk1, hk2, ⟨x, y, h1_eq, h2_eq⟩⟩
      have h3 : 74 * (y : ℤ) + 55 = 7 * k := by 
        linarith [h1_eq, h2_eq]
      have h4 : (k : ℤ) % 74 = 29 := by
        omega
      have h5 : ∃ (t : ℤ), (k : ℤ) = 74 * t + 29 := by
        refine ⟨(k - 29) / 74, ?_⟩
        omega
      rcases h5 with ⟨t, ht⟩
      rw [ht] at hk1 hk2
      have ht1 : t ≥ 14 := by
        omega
      have ht2 : t ≤ 26 := by
        omega
      interval_cases t <;> norm_num at ht <;> norm_num [ht] 
      <;> tauto
    · -- Now assume k is in the right side (the explicit set)
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Show that 1065 is in the left side
        constructor
        · norm_num -- proves 1000 < 1065
        constructor
        · norm_num -- proves 1065 < 2020
        · -- Show ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = 1065
          use 5 * 14 + 3, 7 * 14 + 2
          all_goals omega 
      · -- Show that 1139 is in the left side
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = 1139
          use 5 * 15 + 3, 7 * 15 + 2
          all_goals omega
      · -- Show that 1213 is in the left side
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = 1213
          use 5 * 16 + 3, 7 * 16 + 2
          all_goals omega
      · -- Show that 1287 is in the left side
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = 1287
          use 5 * 17 + 3, 7 * 17 + 2
          all_goals omega
      · -- Show that 1361 is in the left side
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = 1361
          use 5 * 18 + 3, 7 * 18 + 2
          all_goals omega
      · -- Show that 1435 is in the left side
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = 1435
          use 5 * 19 + 3, 7 * 19 + 2
          all_goals omega
      · -- Show that 1509 is in the left side
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = 1509
          use 5 * 20 + 3, 7 * 20 + 2
          all_goals omega
      · -- Show that 1583 is in the left side
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = 1583
          use 5 * 21 + 3, 7 * 21 + 2
          all_goals omega
      · -- Show that 1657 is in the left side
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = 1657
          use 5 * 22 + 3, 7 * 22 + 2
          all_goals omega
      · -- Show that 1731 is in the left side
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = 1731
          use 5 * 23 + 3, 7 * 23 + 2
          all_goals omega
      · -- Show that 1805 is in the left side
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = 1805
          use 5 * 24 + 3, 7 * 24 + 2
          all_goals omega
      · -- Show that 1879 is in the left side
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = 1879
          use 5 * 25 + 3, 7 * 25 + 2
          all_goals omega
      · -- Show that 1953 is in the left side
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show ∃ x y : ℤ, 7 * x - 5 * y = 11 ∧ 5 * x + 7 * y = 1953
          use 5 * 26 + 3, 7 * 26 + 2
          all_goals omega 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }