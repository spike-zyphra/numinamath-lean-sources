import Mathlib

theorem number_theory_98089 :
    Set.ncard {n : ℕ | n > 0 ∧ Even n ∧ 3 ∣ n ∧ n < 2020 ∧ ∃ k, n = k^2} = 7 := by

  have h1 : {n : ℕ | n > 0 ∧ Even n ∧ 3 ∣ n ∧ n < 2020 ∧ ∃ k, n = k^2} = {36, 144, 324, 576, 900, 1296, 1764} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n is in the set of positive even multiples of 3 that are perfect squares less than 2020
      intro h
      rcases h with ⟨h_n_pos, h_n_even, h_div_3, h_n_lt, ⟨k, rfl⟩⟩
      have h1 : k ≤ 44 := by nlinarith
      interval_cases k <;> norm_num at *
      <;> tauto
    · -- Show that the explicit numbers satisfy the required property
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Show 36
        refine ⟨by norm_num, by decide, by norm_num, by norm_num, ⟨6, by norm_num⟩⟩
      · -- Show 144
        refine ⟨by norm_num, by decide, by norm_num, by norm_num, ⟨12, by norm_num⟩⟩
      · -- Show 324
        refine ⟨by norm_num, by decide, by norm_num, by norm_num, ⟨18, by norm_num⟩⟩
      · -- Show 576
        refine ⟨by norm_num, by decide, by norm_num, by norm_num, ⟨24, by norm_num⟩⟩
      · -- Show 900
        refine ⟨by norm_num, by decide, by norm_num, by norm_num, ⟨30, by norm_num⟩⟩
      · -- Show 1296
        refine ⟨by norm_num, by decide, by norm_num, by norm_num, ⟨36, by norm_num⟩⟩
      · -- Show 1764
        refine ⟨by norm_num, by decide, by norm_num, by norm_num, ⟨42, by norm_num⟩⟩
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]