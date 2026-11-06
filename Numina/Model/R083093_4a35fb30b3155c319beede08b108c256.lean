import Mathlib

theorem number_theory_162485 :
    {z : ℕ | Odd z ∧ 3 ∣ z ∧ 5 ∣ z ∧ 7 ∣ z ∧ 500 < z ∧ z < 1000} = {525, 735, 945} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume z satisfies all the conditions; prove z ∈ {525, 735, 945}
    intro h
    rcases h with ⟨hodd, h3, h5, h7, h8, h9⟩
    interval_cases z <;> try { tauto }
    <;> try { contradiction }
  · -- Assume z ∈ {525, 735, 945}; prove it satisfies all the conditions
    rintro (rfl | rfl | rfl)
    · -- Check z = 525
      constructor
      · -- Check it's odd
        exact Nat.odd_iff.mpr (by norm_num)
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check z = 735
      constructor
      · -- Check it's odd
        exact Nat.odd_iff.mpr (by norm_num)
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check z = 945
      constructor
      · -- Check it's odd
        exact Nat.odd_iff.mpr (by norm_num)
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num