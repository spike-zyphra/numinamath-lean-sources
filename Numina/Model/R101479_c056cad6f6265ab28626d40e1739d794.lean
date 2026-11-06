import Mathlib

theorem number_theory_94242 :
    Set.ncard {x : ℕ | x ∈ Finset.Icc 1 100 ∧ 2 ∣ x ∧ 3 ∣ x ∧ 4 ∣ x ∧ 5 ∣ x} = 1 := by
  have h1 : {x : ℕ | x ∈ Finset.Icc 1 100 ∧ 2 ∣ x ∧ 3 ∣ x ∧ 4 ∣ x ∧ 5 ∣ x} = {60} := by
    ext x
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Forward direction: if x is in the set, then x = 60
      intro h
      rcases h with ⟨⟨hx1, hx2⟩, h2, h3, h4, h5⟩
      interval_cases x <;> try { tauto }
      all_goals omega
    · -- Backward direction: if x = 60, then x is in the set
      intro h
      rw [h]
      constructor
      · -- Show 60 is in [1, 100]
        norm_num
      constructor
      · -- Show 60 is divisible by 2
        norm_num
      constructor
      · -- Show 60 is divisible by 3
        norm_num
      constructor
      · -- Show 60 is divisible by 4
        norm_num
      · -- Show 60 is divisible by 5
        norm_num
  rw [h1]
  norm_num