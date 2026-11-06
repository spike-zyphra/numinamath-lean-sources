import Mathlib

theorem number_theory_6423 :
    Set.ncard {l : ℕ | ∃ w : ℕ, l > 7 ∧ w > 7 ∧ l * w = 480 ∧ l > w} = 6 := by
  have h1 : {l : ℕ | ∃ w : ℕ, l > 7 ∧ w > 7 ∧ l * w = 480 ∧ l > w} = {24, 30, 32, 40, 48, 60} := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First, we show that any l in our set must be one of the listed options
      rintro ⟨w, hl, hw, hmul, hlt⟩
      have h : l ≤ 60 := by
        by_contra h'
        push_neg at h'
        -- If l > 60, then w < 8
        have hw1 : w < 8 := by
          nlinarith
        -- But w > 7, which contradicts w < 8
        omega
      interval_cases l <;> omega
    · -- Now, we verify that each of the listed options satisfies our conditions
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- l = 24, w = 20
        use 20
        all_goals norm_num
      · -- l = 30, w = 16
        use 16
        all_goals norm_num
      · -- l = 32, w = 15
        use 15
        all_goals norm_num
      · -- l = 40, w = 12
        use 12
        all_goals norm_num
      · -- l = 48, w = 10
        use 10
        all_goals norm_num
      · -- l = 60, w = 8
        use 8
        all_goals norm_num
  rw [h1]
  norm_num