import Mathlib

theorem number_theory_19505 :
    Set.ncard {x : ℕ | Nat.Prime x ∧ x < 30 ∧ Odd x ∧ x > 0} = 9 := by 
  have h1 : {x : ℕ | Nat.Prime x ∧ x < 30 ∧ Odd x ∧ x > 0} = {3, 5, 7, 11, 13, 17, 19, 23, 29} := by 
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x is prime, x < 30, x is odd, x > 0. Then x ∈ {3, 5, 7, 11, 13, 17, 19, 23, 29}
      intro h
      rcases h with ⟨h_prime, h_lt30, h_odd, h_pos⟩

      interval_cases x <;> try { tauto } <;> contradiction
    · -- Assume x ∈ {3, 5, 7, 11, 13, 17, 19, 23, 29}, then x is prime, x < 30, x is odd, x > 0
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        all_goals norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        all_goals norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        all_goals norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        all_goals norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        all_goals norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        all_goals norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        all_goals norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        all_goals norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        all_goals norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }