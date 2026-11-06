import Mathlib

open Real
open scoped BigOperators

theorem inequalities_4979 :
  Set.ncard {x : ℕ | 0 < x ∧ (2 * x - 9 / 7 : ℝ) < 15} = 8 := by 
  have h1 : {x : ℕ | 0 < x ∧ (2 * x - 9 / 7 : ℝ) < 15} = {1, 2, 3, 4, 5, 6, 7, 8} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x is in the left side, prove it's in the right side
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : (x : ℝ) > 0 := by exact_mod_cast h1
      have h4 : (2 * (x : ℝ) - 9 / 7) < 15 := by linarith
      have h5 : (x : ℝ) < 57 / 7 := by 
        linarith
      have h6 : x ≤ 8 := by
        by_contra h
        push_neg at h
        have h7 : x ≥ 9 := by omega
        have h8 : (x : ℝ) ≥ (9 : ℝ) := by exact_mod_cast h7
        nlinarith
      interval_cases x <;> norm_num at *
    · -- Assume x is in the right side, prove it's in the left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]