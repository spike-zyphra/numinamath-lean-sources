import Mathlib

theorem number_theory_287295_set :
    {n : ℕ | n ∈ Finset.Icc 100 999 ∧ ∃ a : ℕ, n + (Nat.digits 10 n).sum = a * 111} =
    {105, 324, 429, 543, 648, 762, 867, 981} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor 
  · -- Assume n in left side, prove in right side 
    rintro ⟨⟨hn1, hn2⟩, ⟨a, ha⟩⟩ 
    interval_cases n <;> norm_num at ha ⊢ 
    <;> omega 
  · -- Assume n in right side, prove in left side 
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- Show 105 
      constructor 
      · -- Show 105 ∈ [100, 999]
        norm_num 
      · -- Show ∃ a, 105 + (Nat.digits 10 105).sum = a * 111 
        use 1 
        all_goals norm_num 
    · -- Show 324 
      constructor 
      · -- Show 324 ∈ [100, 999]
        norm_num 
      · -- Show ∃ a, 324 + (Nat.digits 10 324).sum = a * 111 
        use 3 
        all_goals norm_num 
    · -- Show 429 
      constructor 
      · -- Show 429 ∈ [100, 999]
        norm_num 
      · -- Show ∃ a, 429 + (Nat.digits 10 429).sum = a * 111 
        use 4 
        all_goals norm_num 
    · -- Show 543 
      constructor 
      · -- Show 543 ∈ [100, 999]
        norm_num 
      · -- Show ∃ a, 543 + (Nat.digits 10 543).sum = a * 111 
        use 5 
        all_goals norm_num 
    · -- Show 648 
      constructor 
      · -- Show 648 ∈ [100, 999]
        norm_num 
      · -- Show ∃ a, 648 + (Nat.digits 10 648).sum = a * 111 
        use 6 
        all_goals norm_num 
    · -- Show 762 
      constructor 
      · -- Show 762 ∈ [100, 999]
        norm_num 
      · -- Show ∃ a, 762 + (Nat.digits 10 762).sum = a * 111 
        use 7 
        all_goals norm_num 
    · -- Show 867 
      constructor 
      · -- Show 867 ∈ [100, 999]
        norm_num 
      · -- Show ∃ a, 867 + (Nat.digits 10 867).sum = a * 111 
        use 8 
        all_goals norm_num 
    · -- Show 981 
      constructor 
      · -- Show 981 ∈ [100, 999]
        norm_num 
      · -- Show ∃ a, 981 + (Nat.digits 10 981).sum = a * 111 
        use 9 
        all_goals norm_num