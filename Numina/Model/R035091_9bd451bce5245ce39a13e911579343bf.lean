import Mathlib

theorem algebra_270853 :
    Set.ncard {x : ℤ | ∃ k : ℕ, 0 ≤ k ∧ k^2 = 25 - x^2} = 7 := by
  have h1 : {x : ℤ | ∃ k : ℕ, 0 ≤ k ∧ k^2 = 25 - x^2} = {-5, -4, -3, 0, 3, 4, 5} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x ∈ {x : ℤ | ∃ k : ℕ, 0 ≤ k ∧ k^2 = 25 - x^2}. Show x ∈ {-5, -4, -3, 0, 3, 4, 5}
      rintro ⟨k, hk1, hk2⟩
      have h2 : k ≤ 5 := by
        have h9 : (k : ℤ) ^ 2 ≤ 25 := by
          have h5 : (k : ℤ)^2 = (25 - x^2 : ℤ) := by
            exact_mod_cast hk2
          nlinarith [sq_nonneg (x : ℤ)]
        have : k ≤ 5 := by
          by_contra h
          push_neg at h
          have : k > 5 := by omega
          have : k ≥ 6 := by omega
          have h3 : (k : ℤ) ≥ 6 := by
            exact_mod_cast (show (k : ℤ) ≥ (6 : ℤ) by omega)
          have h4 : (k : ℤ) ^ 2 ≥ 36 := by
            nlinarith
          nlinarith
        exact_mod_cast (show (k : ℤ) ≤ (5 : ℤ) by linarith)

      have h31 : x ≤ 5 := by
        have h4 : x^2 ≤ 25 := by
          have h3 : (k : ℤ)^2 = (25 - x^2 : ℤ) := by
            exact_mod_cast hk2
          have h4 : (k : ℤ) ^ 2 ≥ 0 := by
            exact sq_nonneg (k : ℤ)
          nlinarith [sq_nonneg (x : ℤ)]
        nlinarith [sq_nonneg x]

      have h32 : x ≥ -5 := by
        have h4 : x^2 ≤ 25 := by
          have h3 : (k : ℤ)^2 = (25 - x^2 : ℤ) := by
            exact_mod_cast hk2
          have h4 : (k : ℤ) ^ 2 ≥ 0 := by
            exact sq_nonneg (k : ℤ)
          nlinarith [sq_nonneg (x : ℤ)]
        nlinarith [sq_nonneg x]

      interval_cases x <;> try { 
        interval_cases k <;> omega
      }
    · -- Assume x ∈ {-5, -4, -3, 0, 3, 4, 5}, show x ∈ {x : ℤ | ∃ k : ℕ, 0 ≤ k ∧ k^2 = 25 - x^2}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = -5
        use 0
        all_goals
        norm_num
      · -- x = -4
        use 3
        all_goals
        norm_num
      · -- x = -3
        use 4
        all_goals
        norm_num
      · -- x = 0
        use 5
        all_goals
        norm_num
      · -- x = 3
        use 4
        all_goals
        norm_num
      · -- x = 4
        use 3
        all_goals
        norm_num
      · -- x = 5
        use 0
        all_goals
        norm_num

  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]