import Mathlib

theorem number_theory_14844 :
    Set.ncard {x : ℕ | x ∈ Finset.Icc 100 300 ∧ 11 ∣ x ∧ 8 ∣ x} = 2 := by
  have h1 : {x : ℕ | x ∈ Finset.Icc 100 300 ∧ 11 ∣ x ∧ 8 ∣ x} = {176, 264} := by
    ext x
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x is in the left side
      rintro ⟨⟨h1, h2⟩, h3, h4⟩
      interval_cases x <;> omega
    · -- Assume x is in the right side
      rintro (rfl | rfl)
      · -- Case x = 176
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Case x = 264
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try native_decide