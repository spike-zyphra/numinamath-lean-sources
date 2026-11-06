import Mathlib

theorem algebra_19998 : Set.ncard {x : ℝ | ∃ n : ℕ, x = 3^(-2 : ℤ) ∧ n = 1 ∨ x = 9^(-2 : ℤ) ∧ n = 2 ∨ x = 27^(-2 / 3 : ℝ) ∧ n = 3 ∨ x = 9 * 81^(-1 : ℤ) ∧ n = 4 ∨ x = 243^(-4 / 5 : ℝ) ∧ n = 5} = 2 := by

  have h1 : {x : ℝ | ∃ n : ℕ, x = 3^(-2 : ℤ) ∧ n = 1 ∨ x = 9^(-2 : ℤ) ∧ n = 2 ∨ x = 27^(-2 / 3 : ℝ) ∧ n = 3 ∨ x = 9 * 81^(-1 : ℤ) ∧ n = 4 ∨ x = 243^(-4 / 5 : ℝ) ∧ n = 5} = { (1 / 9 : ℝ), (1 / 81 : ℝ) } := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]

    constructor
    · -- Assume x is in the left side
      rintro ⟨n, h⟩
      rcases h with (h | h | h | h | h)
      · -- x = 3^(-2 : ℤ)
        norm_num [h] at *
      · -- x = 9^(-2 : ℤ)
        norm_num [h] at *
      · -- x = 27^(-2 / 3 : ℝ)
        have h27 : (27 : ℝ) ^ (-2 / 3 : ℝ) = (1 / 9 : ℝ) := by
          have h1 : (27 : ℝ) ^ (-2 / 3 : ℝ) = ((3 : ℝ) ^ (3 : ℝ)) ^ (-2 / 3 : ℝ) := by norm_num
          rw [h1]
          rw [← Real.rpow_mul]
          norm_num
          all_goals norm_num
        rw [h27] at h
        norm_num [h] at *
      · -- x = 9 * 81^(-1 : ℤ)
        norm_num [h] at *
      · -- x = 243^(-4 / 5 : ℝ)
        have h243 : (243 : ℝ) ^ (-4 / 5 : ℝ) = (1 / 81 : ℝ) := by
          have h1 : (243 : ℝ) ^ (-4 / 5 : ℝ) = ((3 : ℝ) ^ (5 : ℝ)) ^ (-4 / 5 : ℝ) := by norm_num
          rw [h1]
          rw [← Real.rpow_mul]
          norm_num
          all_goals norm_num
        rw [h243] at h
        norm_num [h] at *
    · -- Assume x is in the right side
      rintro (rfl | rfl)
      · -- x = 1/9
        use 1
        norm_num
      · -- x = 1/81
        use 2
        norm_num
  rw [h1]
  norm_num [Set.ncard_pair]
  all_goals norm_num