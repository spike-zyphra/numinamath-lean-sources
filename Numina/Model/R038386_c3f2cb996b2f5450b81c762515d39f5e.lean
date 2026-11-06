import Mathlib

theorem number_theory_100406 :
    Set.ncard {x | ∃ a b c : ℕ, x = a + b + c ∧ 0 ≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧ 0 ≤ c ∧ c ≤ 9 ∧
      45 ∣ 2020000 + 100 * a + 10 * b + c} = 3 := by

  have h1 : {x | ∃ a b c : ℕ, x = a + b + c ∧ 0 ≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧ 0 ≤ c ∧ c ≤ 9 ∧
      45 ∣ 2020000 + 100 * a + 10 * b + c} = {5, 14, 23} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x is in the set on the left side, prove it is in the right side
      rintro ⟨a, b, c, h_eq, ha_1, ha_2, hb_1, hb_2, hc_1, hc_2, h45⟩

      have h5 : (2020000 + 100 * a + 10 * b + c) % 5 = 0 := by
        omega

      have h9 : (2020000 + 100 * a + 10 * b + c) % 9 = 0 := by
        omega

      have h5' : c % 5 = 0 := by
        omega

      have hc0_or_5 : c = 0 ∨ c = 5 := by
        omega

      rcases hc0_or_5 with hc | hc
      · -- Case c = 0
        have h1 : a + b ≤ 18 := by
          omega

        have h2 : (a + b) % 9 = 5 := by
          have h_eq9' : (4 + a + b) % 9 = 0 := by
            omega
          omega

        have h_eq1 : a + b = 5 ∨ a + b = 14 := by
          omega

        have hx : x = 5 ∨ x = 14 := by
          omega
        tauto

      · -- Case c = 5
        have h1 : a + b ≤ 18 := by
          omega

        have h2 : (a + b) % 9 = 0 := by
          have h_eq9' : (9 + a + b) % 9 = 0 := by
            omega
          omega

        have h_eq1 : a + b = 0 ∨ a + b = 9 ∨ a + b = 18 := by
          omega

        have hx : x = 5 ∨ x = 14 ∨ x = 23 := by
          omega
        tauto

    · -- Assume x is in the right side set, prove it is in the left side set.
      rintro (rfl | rfl | rfl)
      · -- Case x = 5
        use 0, 5, 0
        all_goals norm_num

      · -- Case x = 14
        use 4, 5, 5
        all_goals norm_num

      · -- Case x = 23
        use 9, 9, 5
        all_goals norm_num

  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]