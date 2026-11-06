import Mathlib

theorem algebra_10293 : {a : ℤ | a > 0 ∧ {x : ℤ | x > 0 ∧ 2 * x > 3 * x - 3 ∧ 3 * x - a > -6} = {2}}.encard = 3 := by
  have h1 : {a : ℤ | a > 0 ∧ {x : ℤ | x > 0 ∧ 2 * x > 3 * x - 3 ∧ 3 * x - a > -6} = {2}} = {9, 10, 11} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Forward direction: if a in left side, then a in right side
      intro h
      rcases h with ⟨ha_pos, heq⟩
      have h2 : (2 : ℤ) ∈ {x : ℤ | x > 0 ∧ 2 * x > 3 * x - 3 ∧ 3 * x - a > -6} := by
        have h2 : (2 : ℤ) ∈ ( {x : ℤ | x > 0 ∧ 2 * x > 3 * x - 3 ∧ 3 * x - a > -6} : Set ℤ ) := by
          rw [heq]
          simp
        exact h2
      have h3 : a < 12 := by
        simp at h2 ⊢
        omega
      have h1not : (1 : ℤ) ∉ {x : ℤ | x > 0 ∧ 2 * x > 3 * x - 3 ∧ 3 * x - a > -6} := by
        have h1not : (1 : ℤ) ∉ ( {x : ℤ | x > 0 ∧ 2 * x > 3 * x - 3 ∧ 3 * x - a > -6} : Set ℤ ) := by
          rw [heq]
          simp
        exact h1not
      have h4 : a ≥ 9 := by
        simp at h1not ⊢
        omega
      interval_cases a <;> tauto
    · -- Backward direction: if a in right side, then a in left side
      rintro (rfl | rfl | rfl)
      · -- Case 9
        constructor
        · -- Show a is positive
          norm_num
        · -- Show the system has exactly {2} as solution
          have h : {x : ℤ | x > 0 ∧ 2 * x > 3 * x - 3 ∧ 3 * x - 9 > -6} = {2} := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
            constructor
            · -- Assume x in the set
              intro h
              rcases h with ⟨hx_pos, h1, h2⟩
              have h3 : x < 3 := by
                omega
              have h4 : x = 1 ∨ x = 2 := by
                omega
              rcases h4 with (r | r)
              · -- Case x = 1
                exfalso
                omega
              · -- Case x = 2
                omega
            · -- Assume x = 2
              intro h
              rw [h]
              constructor
              · norm_num
              constructor
              · norm_num
              · norm_num
          simpa using h
      · -- Case 10
        constructor
        · -- Show a is positive
          norm_num
        · -- Show the system has exactly {2} as solution
          have h : {x : ℤ | x > 0 ∧ 2 * x > 3 * x - 3 ∧ 3 * x - 10 > -6} = {2} := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
            constructor
            · -- Assume x in the set
              intro h
              rcases h with ⟨hx_pos, h1, h2⟩
              have h3 : x < 3 := by
                omega
              have h4 : x = 1 ∨ x = 2 := by
                omega
              rcases h4 with (r | r)
              · -- Case x = 1
                exfalso
                omega
              · -- Case x = 2
                omega
            · -- Assume x = 2
              intro h
              rw [h]
              constructor
              · norm_num
              constructor
              · norm_num
              · norm_num
          simpa using h
      · -- Case 11
        constructor
        · -- Show a is positive
          norm_num
        · -- Show the system has exactly {2} as solution
          have h : {x : ℤ | x > 0 ∧ 2 * x > 3 * x - 3 ∧ 3 * x - 11 > -6} = {2} := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
            constructor
            · -- Assume x in the set
              intro h
              rcases h with ⟨hx_pos, h1, h2⟩
              have h3 : x < 3 := by
                omega
              have h4 : x = 1 ∨ x = 2 := by
                omega
              rcases h4 with (r | r)
              · -- Case x = 1
                exfalso
                omega
              · -- Case x = 2
                omega
            · -- Assume x = 2
              intro h
              rw [h]
              constructor
              · norm_num
              constructor
              · norm_num
              · norm_num
          simpa using h
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]