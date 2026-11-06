import Mathlib

theorem number_theory_275127 :
    Set.ncard {p : ℕ | ∃ a b, p = a * b ∧ a ≠ b ∧ Even p ∧ a ∈ Finset.Icc 1 5 ∧ b ∈ Finset.Icc 1 5} >
    Set.ncard {p : ℕ | ∃ a b, p = a * b ∧ a ≠ b ∧ Odd p ∧ a ∈ Finset.Icc 1 5 ∧ b ∈ Finset.Icc 1 5} := by 
  have h1 : {p : ℕ | ∃ a b, p = a * b ∧ a ≠ b ∧ Even p ∧ a ∈ Finset.Icc 1 5 ∧ b ∈ Finset.Icc 1 5} = 
    {2, 4, 6, 8, 10, 12, 20} := by
    ext p 
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, 
      Set.mem_singleton_iff]
    constructor 
    · -- Assume p is in the left-hand side set.
      rintro ⟨a, b, h_eq, h_neq, h_even, ha1, ha2⟩
      have h3 : a ≤ 5 := by omega 
      have h4 : b ≤ 5 := by omega 
      interval_cases a <;> interval_cases b 
      <;> norm_num [h_eq, Nat.even_iff] at h_even ⊢ 
      <;> tauto 
    · -- Backward direction.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- p = 2
        exact ⟨1, 2, by norm_num, by norm_num, by decide, by norm_num, by norm_num⟩
      · -- p = 4
        exact ⟨1, 4, by norm_num, by norm_num, by decide, by norm_num, by norm_num⟩
      · -- p = 6
        exact ⟨2, 3, by norm_num, by norm_num, by decide, by norm_num, by norm_num⟩
      · -- p = 8
        exact ⟨2, 4, by norm_num, by norm_num, by decide, by norm_num, by norm_num⟩
      · -- p = 10
        exact ⟨2, 5, by norm_num, by norm_num, by decide, by norm_num, by norm_num⟩
      · -- p = 12
        exact ⟨3, 4, by norm_num, by norm_num, by decide, by norm_num, by norm_num⟩
      · -- p = 20
        exact ⟨4, 5, by norm_num, by norm_num, by decide, by norm_num, by norm_num⟩
  have h2 : {p : ℕ | ∃ a b, p = a * b ∧ a ≠ b ∧ Odd p ∧ a ∈ Finset.Icc 1 5 ∧ b ∈ Finset.Icc 1 5} = 
    {3, 5, 15} := by 
    ext p 
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, 
      Set.mem_singleton_iff]
    constructor 
    · -- Forward direction
      rintro ⟨a, b, h_eq, h_neq, h_odd, ha1, ha2⟩
      have h3 : a ≤ 5 := by omega 
      have h4 : b ≤ 5 := by omega 
      interval_cases a <;> interval_cases b 
      <;> norm_num [h_eq, Nat.odd_iff] at h_odd ⊢ 
      <;> tauto 
    · -- Backward direction
      rintro (rfl | rfl | rfl)
      · -- p = 3
        exact ⟨1, 3, by norm_num, by norm_num, by decide, by norm_num, by norm_num⟩
      · -- p = 5
        exact ⟨1, 5, by norm_num, by norm_num, by decide, by norm_num, by norm_num⟩
      · -- p = 15
        exact ⟨3, 5, by norm_num, by norm_num, by decide, by norm_num, by norm_num⟩
  rw [h1, h2]
  norm_num