import Mathlib

theorem algebra_20863 :
    Set.ncard {x : ℕ | 0 < x ∧ 10 < x ^ 2 + 4 * x + 4 ∧ x ^ 2 + 4 * x + 4 < 50} = 4 := by
  have h1 : {x : ℕ | 0 < x ∧ 10 < x ^ 2 + 4 * x + 4 ∧ x ^ 2 + 4 * x + 4 < 50} = {2, 3, 4, 5} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n is in {x : ℕ | 0 < x ∧ 10 < x ^ 2 + 4 * x + 4 ∧ x ^ 2 + 4 * x + 4 < 50}
      rintro ⟨hn_pos, h1, h2⟩
      have h3 : n > 0 := by linarith
      have h4 : n ≥ 2 := by
        by_contra h
        push_neg at h
        have h5 : n = 1 := by
          omega
        rw [h5] at h1
        all_goals
        nlinarith
      have h5 : n ≤ 5 := by
        by_contra h
        push_neg at h
        have h6 : n ≥ 6 := by
          omega
        nlinarith [h6]
      have : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
        omega
      tauto
    · -- Assume n is in {2, 3, 4, 5}
      rintro (rfl | rfl | rfl | rfl)
      · -- n = 2
        constructor
        · -- Show n > 0
          norm_num
        constructor
        · -- Show 10 < 2^2 + 4 * 2 + 4
          norm_num
        · -- Show 2^2 + 4 * 2 + 4 < 50
          norm_num
      · -- n = 3
        constructor
        · -- Show n > 0
          norm_num
        constructor
        · -- Show 10 < 3^2 + 4 * 3 + 4
          norm_num
        · -- Show 3^2 + 4 * 3 + 4 < 50
          norm_num
      · -- n = 4
        constructor
        · -- Show n > 0
          norm_num
        constructor
        · -- Show 10 < 4^2 + 4 * 4 + 4
          norm_num
        · -- Show 4^2 + 4 * 4 + 4 < 50
          norm_num
      · -- n = 5
        constructor
        · -- Show n > 0
          norm_num
        constructor
        · -- Show 10 < 5^2 + 4 * 5 + 4
          norm_num
        · -- Show 5^2 + 4 * 5 + 4 < 50
          norm_num
  rw [h1]
  norm_num