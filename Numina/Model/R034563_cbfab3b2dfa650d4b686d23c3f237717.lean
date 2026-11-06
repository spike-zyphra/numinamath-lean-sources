import Mathlib

theorem algebra_2673 :
    Set.ncard {a : ℤ | a ≠ 0 ∧ ∃ x : ℤ, a * x = 2 * a ^ 3 - 3 * a ^ 2 - 5 * a + 4} = 6 := by
  have h1 : {a : ℤ | a ≠ 0 ∧ ∃ x : ℤ, a * x = 2 * a ^ 3 - 3 * a ^ 2 - 5 * a + 4} = {1, -1, 2, -2, 4, -4} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Forward implication
      rintro ⟨ha, ⟨x, hx⟩⟩
      have h_eq : a ∣ 4 := by
        use (x - 2 * a^2 + 3 * a + 5)
        linarith [hx]
      have h8 : a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2 ∨ a = 4 ∨ a = -4 := by
        have h5 : a ∣ 4 := h_eq
        have h3 : a ≠ 0 := ha
        have h6 : a ≤ 4 := by
          apply Int.le_of_dvd (by norm_num) h5
        have h8 : a ≥ -4 := by
          have h9 : -a ∣ 4 := by 
            exact Int.neg_dvd.2 h5
          have h10 : -a ≤ 4 := by
            apply Int.le_of_dvd (by norm_num) h9
          have h11 : -a ≥ -4 := by omega
          omega
        interval_cases a <;> try { tauto }
        all_goals tauto
      tauto
    · -- Backward implication
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · use -2
          all_goals norm_num
      · constructor
        · norm_num
        · use -4
          all_goals norm_num
      · constructor
        · norm_num
        · use -1
          all_goals norm_num
      · constructor
        · norm_num
        · use 7
          all_goals norm_num
      · constructor
        · norm_num
        · use 16
          all_goals norm_num
      · constructor
        · norm_num
        · use 38
          all_goals norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]