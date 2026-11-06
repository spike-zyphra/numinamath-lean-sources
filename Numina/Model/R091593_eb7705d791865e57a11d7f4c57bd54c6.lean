import Mathlib

theorem number_theory_167477 :
    (Finset.Icc 1 10).card = 10 ∧
    {n | n ∈ Finset.Icc 1 10 ∧ Nat.Prime n}.ncard = 4 := by
  constructor
  · -- Show that the cardinality of Finset.Icc 1 10 is 10
    simp
    <;> try { native_decide }
  · -- Show that the cardinality of the primes in range 1 to 10 is 4
    have h1 : {n | n ∈ Finset.Icc 1 10 ∧ Nat.Prime n} = {2, 3, 5, 7} := by
      ext n
      simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · -- Assume n is in the set of primes in the range 1 to 10
        intro h
        rcases h with ⟨⟨hn1, hn10⟩, hnp⟩
        interval_cases n <;> norm_num at hnp <;> tauto
      · -- Show that {2, 3, 5, 7} is contained in the set of primes in the range 1 to 10
        rintro (rfl | rfl | rfl | rfl)
        · constructor <;> norm_num
        · constructor <;> norm_num
        · constructor <;> norm_num
        · constructor <;> norm_num
    rw [h1]
    rw [Set.ncard_eq_toFinset_card']
    simp [Set.toFinset]
    <;> try { native_decide }