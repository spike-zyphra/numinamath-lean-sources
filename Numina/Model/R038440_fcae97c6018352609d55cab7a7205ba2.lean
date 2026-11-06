import Mathlib

theorem number_theory_282541_set_form :
  {n | n ∈ Finset.Icc 1000 9999 ∧ n % 2 = 0 ∧ n % 3 = 1 ∧ n % 5 = 3 ∧ n % 7 = 5 ∧ n % 11 = 9} = {2308, 4618, 6928, 9238} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume n in left side, need show n in right side
    intro h
    rcases h with ⟨⟨hn1, hn2⟩, h2, h3, h5, h7, h11⟩
    have h8 : n % 2310 = 2308 := by 
      omega 
    have h9 : n ≤ 9999 := by linarith
    have h10 : n ≥ 1000 := by linarith
    have h11 : n = 2308 ∨ n = 4618 ∨ n = 6928 ∨ n = 9238 := by 
      omega 
    tauto
  · -- Assume n in right side, need show n in left side
    rintro (rfl | rfl | rfl | rfl)
    · -- 2308
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- 4618
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- 6928
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- 9238
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num