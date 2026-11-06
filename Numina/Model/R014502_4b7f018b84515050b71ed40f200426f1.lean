import Mathlib


theorem number_theory_169070 :
    Set.ncard {n | ∃ a b, n = a + b ∧ Nat.lcm a b = 50} = 8 := by
  have h1 : {n | ∃ a b, n = a + b ∧ Nat.lcm a b = 50} = {27, 35, 51, 52, 55, 60, 75, 100} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n ∈ {n | ∃ a b, n = a + b ∧ Nat.lcm a b = 50}
      rintro ⟨a, b, rfl, hl⟩
      have h1 : a ∣ 50 := by
        have h1 : a ∣ Nat.lcm a b := by
          exact Nat.dvd_lcm_left a b
        rw [hl] at h1
        exact h1
      have h2 : b ∣ 50 := by
        have h2 : b ∣ Nat.lcm a b := by
          exact Nat.dvd_lcm_right a b
        rw [hl] at h2
        exact h2
      have h3 : a ≤ 50 := by
        exact Nat.le_of_dvd (by norm_num) h1
      have h4 : b ≤ 50 := by
        exact Nat.le_of_dvd (by norm_num) h2
      interval_cases a <;> interval_cases b
      <;> norm_num [Nat.lcm] at hl ⊢
      <;> omega
    · -- Assume n ∈ {27, 35, 51, 52, 55, 60, 75, 100}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 27
        use 2, 25
        all_goals norm_num [Nat.lcm]
      · -- n = 35
        use 10, 25
        all_goals norm_num [Nat.lcm]
      · -- n = 51
        use 1, 50
        all_goals norm_num [Nat.lcm]
      · -- n = 52
        use 2, 50
        all_goals norm_num [Nat.lcm]
      · -- n = 55
        use 5, 50
        all_goals norm_num [Nat.lcm]
      · -- n = 60
        use 10, 50
        all_goals norm_num [Nat.lcm]
      · -- n = 75
        use 25, 50
        all_goals norm_num [Nat.lcm]
      · -- n = 100
        use 50, 50
        all_goals norm_num [Nat.lcm]

  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]