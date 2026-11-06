import Mathlib

theorem number_theory_96597 :
    (Set.ncard {x : ℕ × ℕ | x.1 ∈ Finset.Icc 1 10 ∧ x.2 ∈ Finset.Icc 1 6 ∧ ∃ k, k^2 = x.1 * x.2}) / (10 * 6) = 11 / 60 := by
  have h1 : {x : ℕ × ℕ | x.1 ∈ Finset.Icc 1 10 ∧ x.2 ∈ Finset.Icc 1 6 ∧ ∃ k, k^2 = x.1 * x.2} = {(1, 1), (1, 4), (2, 2), (3, 3), (4, 1), (4, 4), (5, 5), (6, 6), (8, 2), (9, 1), (9, 4)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, 
      Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · -- Assume h: ⟨a, b⟩ in left.
      rintro ⟨⟨ha1, ha10⟩, ⟨hb1, hb6⟩, ⟨k, hkb⟩⟩
      have h2 : a ≤ 10 := by
        omega
      have h3 : b ≤ 6 := by
        omega
      interval_cases a <;> interval_cases b 
      <;> try { 
        norm_num at hkb ⊢
        all_goals
          try {
            { 
              have : k ≤ 31 := by nlinarith
              interval_cases k <;> norm_num at hkb ⊢ <;> tauto 
            }
          }
        }
    · -- Assume h2: right side.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (1, 1)
        constructor
        · -- a ∈ Icc 1 10
          norm_num
        constructor
        · -- b ∈ Icc 1 6
          norm_num
        · -- ∃ k, k^2 = a * b
          use 1 
          all_goals norm_num
      · -- (1, 4)
        constructor
        · -- a ∈ Icc 1 10
          norm_num
        constructor
        · -- b ∈ Icc 1 6
          norm_num
        · -- ∃ k, k^2 = a * b
          use 2 
          all_goals norm_num
      · -- (2, 2)
        constructor
        · -- a ∈ Icc 1 10
          norm_num
        constructor
        · -- b ∈ Icc 1 6
          norm_num
        · -- ∃ k, k^2 = a * b
          use 2 
          all_goals norm_num
      · -- (3, 3)
        constructor 
        · -- a ∈ Icc 1 10
          norm_num 
        constructor
        · -- b ∈ Icc 1 6
          norm_num
        · -- ∃ k, k^2 = a * b
          use 3 
          all_goals norm_num
      · -- (4, 1)
        constructor 
        · -- a ∈ Icc 1 10
          norm_num 
        constructor
        · -- b ∈ Icc 1 6
          norm_num 
        · -- ∃ k, k^2 = a * b
          use 2 
          all_goals norm_num
      · -- (4, 4)
        constructor 
        · -- a ∈ Icc 1 10
          norm_num 
        constructor
        · -- b ∈ Icc 1 6
          norm_num 
        · -- ∃ k, k^2 = a * b
          use 4 
          all_goals norm_num
      · -- (5, 5)
        constructor 
        · -- a ∈ Icc 1 10
          norm_num 
        constructor 
        · -- b ∈ Icc 1 6
          norm_num 
        · -- ∃ k, k^2 = a * b
          use 5 
          all_goals norm_num
      · -- (6, 6)
        constructor 
        · -- a ∈ Icc 1 10
          norm_num 
        constructor 
        · -- b ∈ Icc 1 6
          norm_num 
        · -- ∃ k, k^2 = a * b
          use 6 
          all_goals norm_num
      · -- (8, 2)
        constructor 
        · -- a ∈ Icc 1 10
          norm_num 
        constructor 
        · -- b ∈ Icc 1 6
          norm_num 
        · -- ∃ k, k^2 = a * b
          use 4 
          all_goals norm_num
      · -- (9, 1)
        constructor 
        · -- a ∈ Icc 1 10
          norm_num 
        constructor 
        · -- b ∈ Icc 1 6
          norm_num 
        · -- ∃ k, k^2 = a * b
          use 3 
          all_goals norm_num
      · -- (9, 4)
        constructor 
        · -- a ∈ Icc 1 10
          norm_num 
        constructor 
        · -- b ∈ Icc 1 6
          norm_num 
        · -- ∃ k, k^2 = a * b
          use 6 
          all_goals norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
  <;> try { native_decide }
  all_goals tauto