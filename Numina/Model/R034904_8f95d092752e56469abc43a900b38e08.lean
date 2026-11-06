import Mathlib

theorem algebra_21851 (S : Finset ℕ) (hS : S = {1, 5, 25}) :
    {x | ∃ T : Finset ℕ, T ⊆ S ∧ T.card ≥ 2 ∧ x = T.sum id}.encard = 4 := by
  rw [hS]
  have : {x | ∃ T : Finset ℕ, T ⊆ ({1, 5, 25} : Finset ℕ) ∧ T.card ≥ 2 ∧ x = T.sum id} = {6, 26, 30, 31} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First direction: if x is in the left side, it must be in the right side
      rintro ⟨T, hT_sub, hT_card, hx⟩
      have h5 : T ∈ (Finset.powerset ({1, 5, 25} : Finset ℕ)).filter (fun s => s.card ≥ 2) := by 
        simp [Finset.mem_powerset] at *
        all_goals tauto
      have h6 : (Finset.powerset ({1, 5, 25} : Finset ℕ)).filter (fun s => s.card ≥ 2) = {
          {1,5}, {1,25}, {5,25}, {1,5,25}
      } := by
        native_decide
      rw [h6] at h5
      simp at h5
      rcases h5 with (rfl | rfl | rfl | rfl)
      · -- T = {1,5}
        norm_num [Finset.sum_insert, Finset.sum_singleton] at hx ⊢
        all_goals tauto
      · -- T = {1,25}
        norm_num [Finset.sum_insert, Finset.sum_singleton] at hx ⊢
        all_goals tauto
      · -- T = {5,25}
        norm_num [Finset.sum_insert, Finset.sum_singleton] at hx ⊢
        all_goals tauto
      · -- T = {1,5,25}
        norm_num [Finset.sum_insert, Finset.sum_singleton] at hx ⊢
        all_goals tauto
    · -- Now the reverse direction
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 6
        use {1,5}
        constructor
        · -- Show {1,5} ⊆ {1,5,25}
          native_decide
        constructor
        · -- Show card >= 2
          native_decide
        · -- Show sum = 6
          all_goals native_decide
      · -- x = 26
        use {1,25}
        constructor
        · -- Show {1,25} ⊆ {1,5,25}
          native_decide
        constructor
        · -- Show card >= 2
          native_decide
        · -- Show sum = 26
          all_goals native_decide
      · -- x = 30
        use {5,25}
        constructor
        · -- Show {5,25} ⊆ {1,5,25}
          native_decide
        constructor
        · -- Show card >= 2
          native_decide
        · -- Show sum = 30
          all_goals native_decide
      · -- x = 31
        use {1,5,25}
        constructor
        · -- Show {1,5,25} ⊆ {1,5,25}
          native_decide
        constructor
        · -- Show card >= 2
          native_decide
        · -- Show sum = 31
          all_goals native_decide
  rw [this]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]