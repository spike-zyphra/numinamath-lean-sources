import Mathlib

theorem algebra_17143 : {x : ℤ | Odd x ∧ (17 : ℝ) / 4 < x ∧ x < (35 : ℝ) / 2}.ncard = 7 := by 
  have h1 : {x : ℤ | Odd x ∧ (17 : ℝ) / 4 < x ∧ x < (35 : ℝ) / 2} = {5, 7, 9, 11, 13, 15, 17} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x is in the set
      rintro ⟨hx1, hx2, hx3⟩
      have h4 : 4 < x := by
        by_contra h
        push_neg at h
        have h5 : x ≤ 4 := by omega
        have h6 : (x : ℝ) ≤ (4 : ℝ) := by
          exact_mod_cast h5
        norm_num at hx2
        nlinarith
      have h5 : x < 18 := by
        by_contra h
        push_neg at h
        have h6 : x ≥ 18 := by omega
        have h7 : (x : ℝ) ≥ (18 : ℝ) := by
          exact_mod_cast h6
        norm_num at hx3
        nlinarith
      have h8 : x % 2 = 1 := by 
        obtain ⟨k, hk⟩ := hx1
        omega
      interval_cases x <;> norm_num at *
      <;> try { tauto }
    · -- Assume x is in {5, 7, 9, 11, 13, 15, 17}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 5
        constructor
        · -- 5 is odd
          decide
        constructor
        · -- (17 : ℝ) / 4 < (5 : ℝ)
          norm_num
        · -- (5 : ℝ) < (35 : ℝ) / 2
          norm_num
      · -- x = 7
        constructor
        · -- 7 is odd
          decide
        constructor
        · -- (17 : ℝ) / 4 < (7 : ℝ)
          norm_num
        · -- (7 : ℝ) < (35 : ℝ) / 2
          norm_num
      · -- x = 9
        constructor
        · -- 9 is odd
          decide
        constructor
        · -- (17 : ℝ) / 4 < (9 : ℝ)
          norm_num
        · -- (9 : ℝ) < (35 : ℝ) / 2
          norm_num
      · -- x = 11
        constructor
        · -- 11 is odd
          decide
        constructor
        · -- (17 : ℝ) / 4 < (11 : ℝ)
          norm_num
        · -- (11 : ℝ) < (35 : ℝ) / 2
          norm_num
      · -- x = 13
        constructor
        · -- 13 is odd
          decide
        constructor
        · -- (17 : ℝ) / 4 < (13 : ℝ)
          norm_num
        · -- (13 : ℝ) < (35 : ℝ) / 2
          norm_num
      · -- x = 15
        constructor
        · -- 15 is odd
          decide
        constructor
        · -- (17 : ℝ) / 4 < (15 : ℝ)
          norm_num
        · -- (15 : ℝ) < (35 : ℝ) / 2
          norm_num
      · -- x = 17
        constructor
        · -- 17 is odd
          decide
        constructor
        · -- (17 : ℝ) / 4 < (17 : ℝ)
          norm_num
        · -- (17 : ℝ) < (35 : ℝ) / 2
          norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }