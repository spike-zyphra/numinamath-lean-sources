import Mathlib

theorem number_theory_247209 :
    IsGreatest {x | ∃ a b : ℕ, a ≠ b ∧ x = a * b ∧ a ∈ Finset.Icc 0 9 ∧ b ∈ Finset.Icc 0 9} (9 * 8) ∧
    IsLeast {x | ∃ a b : ℕ, a ≠ b ∧ x = a + b ∧ a ∈ Finset.Icc 0 9 ∧ b ∈ Finset.Icc 0 9} (0 + 1) ∧
    {p : Finset ℕ | p.card = 2 ∧ ∃ a b : ℕ, a ≠ b ∧ p = {a, b} ∧ a ∈ Finset.Icc 0 9 ∧ b ∈ Finset.Icc 0 9 ∧ a + b = 10}.ncard = 4 := by
  constructor
  · -- Show that 72 is the greatest element in the set of products of distinct digits
    constructor
    · -- Show that 72 is in the set.
      use 9, 8
      all_goals
        simp
    · -- Show that 72 is greatest in the set.
      intro x hx
      rcases hx with ⟨a, b, hab, hx, ha, hb⟩
      rw [Finset.mem_Icc] at ha hb
      rcases ha with ⟨ha0, ha9⟩
      rcases hb with ⟨hb0, hb9⟩
      by_contra h
      push_neg at h
      have h1 : a ≤ 9 := by linarith
      have h2 : b ≤ 9 := by linarith
      interval_cases a <;> interval_cases b
      <;> omega
  constructor
  · -- Show that 1 is the least element in the set of sums of distinct digits
    constructor
    · -- Show that 1 is in the set.
      use 0, 1
      all_goals
        simp
    · -- Show that 1 is least in the set.
      intro x hx
      rcases hx with ⟨a, b, hab, hx, ha, hb⟩
      rw [Finset.mem_Icc] at ha hb
      rcases ha with ⟨ha0, ha9⟩
      rcases hb with ⟨hb0, hb9⟩
      by_contra h
      push_neg at h
      have h1 : a ≤ 9 := by linarith
      have h2 : b ≤ 9 := by linarith
      omega
  · -- Prove that the cardinality of pairs {a, b} such that a + b = 10 and a ≠ b, a, b ∈ [0, 9], is 4.
    have h1 : {p : Finset ℕ | p.card = 2 ∧ ∃ a b : ℕ, a ≠ b ∧ p = {a, b} ∧ a ∈ Finset.Icc 0 9 ∧ b ∈ Finset.Icc 0 9 ∧ a + b = 10} = 
      ({ {1, 9}, {2, 8}, {3, 7}, {4, 6} } : Set (Finset ℕ)) := by 
      ext p 
      simp only [Finset.mem_insert, Finset.mem_singleton, Set.mem_setOf_eq, Set.mem_insert_iff, 
        Set.mem_singleton_iff]
      constructor
      · -- Assume p is in the first set, prove it's in the second.
        rintro ⟨hp2, a, b, hab, hp, ha, hb, hab10⟩
        rw [Finset.mem_Icc] at ha hb
        rcases ha with ⟨ha0, ha9⟩
        rcases hb with ⟨hb0, hb9⟩
        have h_eq : a + b = 10 := hab10
        have hp_eq : p = {a, b} := hp
        have : a ≤ 9 := by linarith
        have : b ≤ 9 := by linarith
        have h1 : b = 10 - a := by omega
        interval_cases a <;> norm_num [h1] at *
        <;> norm_num [hp_eq] at *
        <;> try { 
          simp [Finset.ext_iff] at *
          <;> tauto 
        }
        <;> try { omega } <;> try { tauto }
      · -- Assume p is in the second set, prove it's in the first.
        rintro (rfl | rfl | rfl | rfl)
        · -- Show that {1, 9} is in the first set.
          constructor
          · -- Show that {1, 9}.card = 2.
            native_decide
          · -- Show existence of a=1, b=9.
            use 1, 9
            all_goals
              simp
        · -- Show that {2, 8} is in the first set.
          constructor
          · -- Show that {2, 8}.card = 2.
            native_decide
          · -- Show existence of a=2, b=8.
            use 2, 8
            all_goals
              simp
        · -- Show that {3, 7} is in the first set.
          constructor
          · -- Show that {3, 7}.card = 2.
            native_decide
          · -- Show existence of a=3, b=7.
            use 3, 7
            all_goals
              simp
        · -- Show that {4, 6} is in the first set.
          constructor
          · -- Show that {4, 6}.card = 2.
            native_decide
          · -- Show existence of a=4, b=6.
            use 4, 6
            all_goals
              simp
    rw [h1]
    rw [Set.ncard_eq_toFinset_card']
    simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
    <;> try { native_decide }