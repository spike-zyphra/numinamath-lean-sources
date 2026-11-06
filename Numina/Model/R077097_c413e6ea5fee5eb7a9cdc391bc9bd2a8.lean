import Mathlib

theorem number_theory_588 :
    {x : ℕ | ∃ a b, x = a * b ∧ a ≠ b ∧ a ∈ Finset.Icc 1 5 ∧ b ∈ Finset.Icc 1 5 ∧ Even x}.ncard > {x : ℕ | ∃ a b, x = a * b ∧ a ≠ b ∧ a ∈ Finset.Icc 1 5 ∧ b ∈ Finset.Icc 1 5 ∧ Odd x}.ncard := by
  have h1 : {x : ℕ | ∃ a b, x = a * b ∧ a ≠ b ∧ a ∈ Finset.Icc 1 5 ∧ b ∈ Finset.Icc 1 5 ∧ Even x} = {2, 4, 6, 8, 10, 12, 20} := by
    ext x
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x is even product.
      rintro ⟨a, b, hx_eq, hneq, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩, heven⟩
      interval_cases a <;> interval_cases b <;> simp [hx_eq, Nat.even_iff] at heven ⊢ <;> omega
    · -- Assume x ∈ {2,4,6,8,10,12,20}.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 2
        use 1, 2
        all_goals simp
        <;> try native_decide
      · -- x = 4
        use 1, 4
        all_goals simp
        <;> try native_decide
      · -- x = 6
        use 2, 3
        all_goals simp
        <;> try native_decide
      · -- x = 8
        use 2, 4
        all_goals simp
        <;> try native_decide
      · -- x = 10
        use 2, 5
        all_goals simp
        <;> try native_decide
      · -- x = 12
        use 3, 4
        all_goals simp
        <;> try native_decide
      · -- x = 20
        use 4, 5
        all_goals simp
        <;> try native_decide
  have h2 : {x : ℕ | ∃ a b, x = a * b ∧ a ≠ b ∧ a ∈ Finset.Icc 1 5 ∧ b ∈ Finset.Icc 1 5 ∧ Odd x} = {3, 5, 15} := by
    ext x
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x is odd product.
      rintro ⟨a, b, hx_eq, hneq, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hodd⟩
      interval_cases a <;> interval_cases b <;> simp [hx_eq, Nat.odd_iff] at hodd ⊢ <;> omega
    · -- Assume x ∈ {3,5,15}
      rintro (rfl | rfl | rfl)
      · -- x = 3
        use 1, 3
        all_goals simp
        <;> try native_decide
      · -- x = 5
        use 1, 5
        all_goals simp
        <;> try native_decide
      · -- x = 15
        use 3, 5
        all_goals simp
        <;> try native_decide
  rw [h1, h2]
  rw [Set.ncard_eq_toFinset_card']
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.Icc]
  <;> try native_decide