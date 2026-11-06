import Mathlib

theorem number_theory_16468 :
    {x : ℤ | x ∈ Finset.Icc 1 6 ∧ ∀ a b : ℤ, 3 * b = 8 - 2 * a → x ∣ 2 * b + 12}.ncard = 3 := by
  have h1 : {x : ℤ | x ∈ Finset.Icc 1 6 ∧ ∀ a b : ℤ, 3 * b = 8 - 2 * a → x ∣ 2 * b + 12} = {1, 2, 4} := by
    ext x
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First implication: if x in the set, then x is in {1, 2, 4}
      rintro ⟨⟨hx1, hx2⟩, hx3⟩
      have h2 := hx3 1 2 (by norm_num)
      have h3 : x ∣ 16 := by
        norm_num at h2 ⊢
        exact h2
      interval_cases x <;> norm_num at h3 ⊢ <;> try tauto
    · -- Second implication: if x is in {1, 2, 4}, then it's in the set
      rintro (rfl | rfl | rfl)
      · -- Show that 1 is in the set
        constructor
        · norm_num
        · intro a b h
          norm_num
      · -- Show that 2 is in the set
        constructor
        · norm_num
        · intro a b h
          have h2 : (2 : ℤ) ∣ 2 * b + 12 := by
            use (b + 6)
            all_goals linarith
          exact h2
      · -- Show that 4 is in the set
        constructor
        · norm_num
        · intro a b h
          have h2 : (4 : ℤ) ∣ 2 * b + 12 := by
            have h4 : b % 2 = 0 := by
              omega
            have h3b : ∃ k, b = 2 * k := by
              refine' ⟨b / 2, by omega⟩
            rcases h3b with ⟨k, hk⟩
            use k + 3
            linarith [hk]
          exact h2
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> rfl