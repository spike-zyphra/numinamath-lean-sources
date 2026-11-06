import Mathlib

theorem number_theory_177795 :
    {z : ℕ | z ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 z).length = 3 ∧
      (Nat.digits 10 z).toFinset.card = 3 ∧ (Nat.digits 10 z).sum = 11 ∧ 11 ∣ z} =
    {209, 308, 407, 506, 605, 704, 803, 902} := by
  ext z
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First, prove the forward implication: if z is in the set, then z is in {209, 308, 407, 506, 605, 704, 803, 902}
    rintro ⟨⟨hz1, hz2⟩, h1, h2, h3, h4⟩
    interval_cases z <;> norm_num at h4 h3 h1 h2 ⊢ 
  · -- Now prove the reverse: if z is in {209, 308, 407, 506, 605, 704, 803, 902}, then it's in the set.
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      native_decide