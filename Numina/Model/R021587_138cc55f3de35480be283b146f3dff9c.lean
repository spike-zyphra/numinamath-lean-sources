import Mathlib

theorem number_theory_288694 : {i | i ∈ Finset.range (Nat.digits 10 (20^10)).length ∧ (Nat.digits 10 (20^10))[i]! = 0}.ncard = 11 := by 
  have h1 : 20^10 = 10240000000000 := by norm_num
  rw [h1]
  have h2 : Nat.digits 10 (10240000000000 : ℕ) = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 1] := by
    norm_num
  have h3 : {i | i ∈ Finset.range (Nat.digits 10 (10240000000000 : ℕ)).length ∧ (Nat.digits 10 (10240000000000 : ℕ))[i]! = 0} = 
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12} := by
    ext i
    simp [h2]
    constructor
    · -- First, show that if i is in the set, then i ∈ {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12}
      intro h
      rcases h with ⟨h4, h5⟩
      interval_cases i <;> try simp at h5 ⊢ <;> tauto
    · -- Now the reverse direction.
      intro h
      rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        simp
  rw [h3]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  all_goals try { native_decide }