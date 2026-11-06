import Mathlib

theorem number_theory_166060 : {z : ℕ | 1000 ≤ z ∧ z ≤ 1700 ∧ 9 ∣ z ∧ 12 ∣ z ∧ 14 ∣ z} = {1008, 1260, 1512} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume z is in the left side, so must be on the right
    intro h
    rcases h with ⟨h₁, h₂, h₃, h₄, h₅⟩
    interval_cases z <;> norm_num at *
    <;> omega
  · -- Assume z is in the right side, so must be on the left
    rintro (rfl | rfl | rfl)
    · constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num