import Mathlib

theorem number_theory_183785 :
    {n : ℕ | n ∈ Finset.Icc 100 999 ∧ 9 ∣ n ∧ (Nat.digits 10 n).all (Nat.Prime ·)} =
    {225, 252, 522, 333} := by 
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Assume n in left side, prove in right side
    intro h
    rcases h with ⟨⟨hn1, hn2⟩, hn3, hn4⟩
    interval_cases n <;> norm_num at *
    <;> try trivial
    <;> norm_num at hn4 ⊢ <;> try trivial
  · -- Assume n in right side, prove in left side
    rintro (rfl | rfl | rfl | rfl)
    · constructor
      · norm_num
      constructor
      · norm_num
      · native_decide
    · constructor
      · norm_num
      constructor
      · norm_num
      · native_decide
    · constructor
      · norm_num
      constructor
      · norm_num
      · native_decide
    · constructor
      · norm_num
      constructor
      · norm_num
      · native_decide