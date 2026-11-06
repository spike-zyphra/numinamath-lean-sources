import Mathlib

theorem number_theory_135504 :
    Set.ncard {m : ℕ | 10 ≤ m ∧ m ≤ 99 ∧ ∃ A B C : ℕ, A < 10 ∧ B < 10 ∧ C < 10 ∧
      3 * m = 100 * A + 10 * B + C ∧ 4 * m = 100 * C + 10 * A + B} = 3 := by

  have h1 : {m : ℕ | 10 ≤ m ∧ m ≤ 99 ∧ ∃ A B C : ℕ, A < 10 ∧ B < 10 ∧ C < 10 ∧
    3 * m = 100 * A + 10 * B + C ∧ 4 * m = 100 * C + 10 * A + B} = {27, 54, 81} := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume m in left side set, prove it in {27, 54, 81}
      rintro ⟨h1, h2, ⟨A, B, C, hA, hB, hC, h3, h4⟩⟩
      have h5 : m ≥ 10 := h1
      have h6 : m ≤ 99 := h2

      interval_cases m <;> try { 
        omega
      } <;> omega

      all_goals 
        omega

    · -- Assume m in {27, 54, 81}, prove it in left side set
      rintro (rfl | rfl | rfl)
      · constructor
        · norm_num
        constructor
        · norm_num
        · -- exists A, B, C
          use 0, 8, 1
          all_goals norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · -- exists A, B, C
          use 1, 6, 2
          all_goals norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · -- exists A, B, C
          use 2, 4, 3
          all_goals norm_num
  rw [h1]
  norm_num