import Mathlib

theorem number_theory_230983 :
    {x : ℕ | x ≠ 0 ∧ 1200 % x = 3 ∧ 1640 % x = 2 ∧ 1960 % x = 7} =
    {9, 21, 63} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- First, if x divides the numbers with those remainders, it's in {9, 21, 63}
    intro h
    rcases h with ⟨hx1, h1, h2, h3⟩
    have h4 : x ≤ 1960 := by
      by_contra h
      push_neg at h
      have h5 : 1960 % x = 1960 := by
        rw [Nat.mod_eq_of_lt]
        all_goals linarith
      omega -- contradiction with h3 (1960 % x = 7)
    interval_cases x <;> norm_num at h1 h2 h3 ⊢
    <;> tauto 
  · -- Now, show that {9,21,63} must satisfy all congruences
    rintro (rfl | rfl | rfl)
    · -- x = 9
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num 
    · -- x = 21
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num 
    · -- x = 63
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num