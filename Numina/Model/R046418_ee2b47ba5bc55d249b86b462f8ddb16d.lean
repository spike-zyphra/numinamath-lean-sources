import Mathlib

theorem number_theory_273453 :
    Set.ncard {x | x > 1 ∧ IsSquare x ∧ x ∣ 128} = 3 := by
  have h1 : {x | x > 1 ∧ IsSquare x ∧ x ∣ 128} = {4, 16, 64} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x in {x | x > 1 ∧ IsSquare x ∧ x ∣ 128}, prove x in {4, 16, 64}
      intro h
      rcases h with ⟨hx1, hsq, hdiv⟩
      have h2 : x ≤ 128 := by
        exact Nat.le_of_dvd (by norm_num) hdiv
      have h3 : x ≤ 128 := h2
      have h4 : x ∣ 128 := hdiv
      have h5 : x > 1 := hx1
      have h6 : IsSquare x := hsq
      rcases h6 with ⟨y, hy⟩
      have h7 : x = y ^ 2 := by
        linarith
      have h8 : y ^ 2 > 1 := by
        nlinarith
      have h9 : y ≤ 11 := by
        by_contra h
        push_neg at h
        have h10 : y ≥ 12 := by
          omega
        nlinarith
      have h11 : y ≥ 2 := by
        by_contra h
        push_neg at h
        have : y < 2 := by omega
        interval_cases y <;> omega
      interval_cases y <;> norm_num [h7] at *
      all_goals tauto
    · -- Assume x in {4, 16, 64}, prove x in {x | x > 1 ∧ IsSquare x ∧ x ∣ 128}
      rintro (rfl | rfl | rfl)
      · -- Show that 4 is in the set
        constructor
        · norm_num
        constructor
        · native_decide
        · norm_num
      · -- Show that 16 is in the set
        constructor
        · norm_num
        constructor
        · native_decide
        · norm_num
      · -- Show that 64 is in the set
        constructor
        · norm_num
        constructor
        · native_decide
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> try { native_decide }