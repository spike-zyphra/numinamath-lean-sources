import Mathlib

open Real Set
open scoped BigOperators

theorem number_theory_301376 :
  ∑ x in (Finset.Icc 1 24).filter (fun y => y < 24 ∧ Nat.Coprime y 24), cos (x * π / 24) = 0 := by
  have h2 : (Finset.Icc 1 24).filter (fun y => y < 24 ∧ Nat.Coprime y 24) = 
    {1, 5, 7, 11, 13, 17, 19, 23} := by
    ext n
    simp
    constructor
    · -- Assume n in {x ∈ Finset.Icc 1 24 | y < 24 ∧ Nat.Coprime y 24}
      intro h
      rcases h with ⟨⟨hn1, hn2⟩, ⟨hn3, hn4⟩⟩
      interval_cases n <;> norm_num at *
    · -- Show that if n in {1,5,7,11,13,17,19,23}, then it is in the filtered set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 1
        constructor <;> norm_num
      · -- n = 5
        constructor <;> norm_num
      · -- n = 7
        constructor <;> norm_num
      · -- n = 11
        constructor <;> norm_num
      · -- n = 13
        constructor <;> norm_num
      · -- n = 17
        constructor <;> norm_num
      · -- n = 19
        constructor <;> norm_num
      · -- n = 23
        constructor <;> norm_num
  rw [h2]
  have h3 : cos (1 * π / 24) + cos (23 * π / 24) = 0 := by
    have h1 : cos (23 * π / 24) = -cos (1 * π / 24) := by
      have h4 : 23 * π / 24 = π - 1 * π / 24 := by
        linarith
      rw [h4]
      have h5 : cos (π - 1 * π / 24) = -cos (1 * π / 24) := by 
        rw [cos_pi_sub]
      linarith
    linarith
  have h4 : cos (5 * π / 24) + cos (19 * π / 24) = 0 := by
    have h2 : cos (19 * π / 24) = -cos (5 * π / 24) := by
      have h4 : 19 * π / 24 = π - 5 * π / 24 := by 
        linarith
      rw [h4]
      have h5 : cos (π - 5 * π / 24) = -cos (5 * π / 24) := by 
        rw [cos_pi_sub]
      linarith
    linarith
  have h5 : cos (7 * π / 24) + cos (17 * π / 24) = 0 := by
    have h2 : cos (17 * π / 24) = -cos (7 * π / 24) := by
      have h4 : 17 * π / 24 = π - 7 * π / 24 := by 
        linarith
      rw [h4]
      have h5 : cos (π - 7 * π / 24) = -cos (7 * π / 24) := by 
        rw [cos_pi_sub]
      linarith
    linarith
  have h6 : cos (11 * π / 24) + cos (13 * π / 24) = 0 := by
    have h2 : cos (13 * π / 24) = -cos (11 * π / 24) := by
      have h4 : 13 * π / 24 = π - 11 * π / 24 := by 
        linarith
      rw [h4]
      have h5 : cos (π - 11 * π / 24) = -cos (11 * π / 24) := by 
        rw [cos_pi_sub]
      linarith
    linarith
  norm_num [Finset.sum_insert, Finset.sum_singleton] at *
  all_goals linarith [h3, h4, h5, h6]