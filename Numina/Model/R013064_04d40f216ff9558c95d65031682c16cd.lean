import Mathlib

theorem number_theory_187202 : {x : ℕ | x ∈ Finset.Icc 1 100 ∧ 2 ∣ x ∧ 3 ∣ x ∧ 4 ∣ x ∧ 5 ∣ x}.encard = 1 := by 
  have h1 : {x : ℕ | x ∈ Finset.Icc 1 100 ∧ 2 ∣ x ∧ 3 ∣ x ∧ 4 ∣ x ∧ 5 ∣ x} = {60} := by
    ext x
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor 
    · -- Assume x in the set, prove x = 60
      rintro ⟨⟨hx1, hx2⟩, h2, h3, h4, h5⟩
      interval_cases x <;> norm_num at h2 h3 h4 h5 hx1 hx2 ⊢ <;> omega
    · -- Assume x = 60, prove in the set
      intro h
      rw [h]
      constructor 
      · -- Show 60 ∈ Finset.Icc 1 100
        norm_num
      constructor 
      · norm_num
      constructor 
      · norm_num
      constructor 
      · norm_num
      · norm_num
  rw [h1]
  simp [Set.encard_singleton]