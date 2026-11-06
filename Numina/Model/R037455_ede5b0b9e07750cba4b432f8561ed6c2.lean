import Mathlib

theorem number_theory_258036 :
  {n : ℕ | n ≥ 100 ∧ n ≤ 999 ∧ n = 34 * (Nat.digits 10 n).sum} =
  {102, 204, 306, 408} := by 
  ext n 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume n is in the left side set
    rintro ⟨h1, h2, heq⟩
    interval_cases n <;> norm_num at heq ⊢ <;> tauto
  · -- Assume n is in the right side set
    rintro (rfl | rfl | rfl | rfl)
    · -- Show n=102 is in the left side set
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Show n=204 is in the left side set 
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num
    · -- Show n=306 is in the left side set 
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num 
    · -- Show n=408 is in the left side set 
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num