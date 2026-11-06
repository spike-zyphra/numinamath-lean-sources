import Mathlib

open Classical in
theorem number_theory_11025 : ((Finset.range 9).filter fun n => ∃ m, m * n % 9 = 1).card = 6 := by 
  have h1 : (Finset.range 9).filter (fun n => ∃ m, m * n % 9 = 1) = {1, 2, 4, 5, 7, 8} := by 
    ext n 
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor 
    · -- Assume that n in the filter, show n ∈ {1, 2, 4, 5, 7, 8}
      intro h
      rcases h with ⟨hn1, hn2⟩
      have h3 : n < 9 := by 
        omega 
      have h4 : n ≤ 8 := by 
        omega
      interval_cases n <;> simp_all [Finset.mem_insert, Finset.mem_singleton] 
      <;> try { tauto }
      <;> try { trivial }
      <;> try { 
        omega 
      }
      <;> try { 
        exfalso 
        <;> try { contradiction }
      }
    · -- Show if n ∈ {1,2,4,5,7,8}, then n in the filter.
      intro h 
      rcases h with (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 1
        constructor 
        · norm_num
        · use 1
          all_goals norm_num 
      · -- n = 2
        constructor
        · norm_num 
        · use 5
          all_goals norm_num 
      · -- n = 4
        constructor
        · norm_num 
        · use 7
          all_goals norm_num 
      · -- n = 5
        constructor
        · norm_num 
        · use 2
          all_goals norm_num 
      · -- n = 7
        constructor
        · norm_num 
        · use 4
          all_goals norm_num 
      · -- n = 8
        constructor
        · norm_num 
        · use 8
          all_goals norm_num 
  rw [h1]
  native_decide