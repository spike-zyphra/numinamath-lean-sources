import Mathlib

theorem number_theory_243940 : {n | n ∈ Finset.Icc 6 10 ∧ (2^2024 + 2^2023 + 2^2022) % n = 0}.encard = 2 := by
  have h1 : {n | n ∈ Finset.Icc 6 10 ∧ (2^2024 + 2^2023 + 2^2022) % n = 0} = {7, 8} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Forward direction: if n is in the set, then n = 7 or 8
      intro h
      rcases h with ⟨⟨hn1, hn2⟩, hdiv⟩
      have h2 : n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 := by
        omega
      rcases h2 with (rfl | rfl | rfl | rfl | rfl)
      · -- n = 6
        norm_num at hdiv
      · -- n = 7
        norm_num at hdiv hn1 hn2
        all_goals tauto
      · -- n = 8
        norm_num at hdiv hn1 hn2
        all_goals tauto
      · -- n = 9
        norm_num at hdiv
      · -- n = 10
        norm_num at hdiv
    · -- Backward direction: if n = 7 or 8, then n is in the set
      rintro (rfl | rfl)
      · -- n = 7
        constructor
        · -- Show 7 is in the range [6, 10]
          norm_num
        · -- Show 7 divides the sum
          norm_num
      · -- n = 8
        constructor
        · -- Show 8 is in the range [6, 10]
          norm_num
        · -- Show 8 divides the sum
          norm_num
  rw [h1]
  rw [Set.encard_pair]
  all_goals norm_num