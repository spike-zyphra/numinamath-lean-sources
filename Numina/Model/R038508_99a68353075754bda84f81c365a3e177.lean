import Mathlib

theorem algebra_265610 :
    Set.ncard {k : ℤ | ∃ x y : ℤ, k * x - 5 * y + 7 = 0 ∧ k ^ 2 * x - 5 * y + 1 = 0} = 2 := by
  have h1 : {k : ℤ | ∃ x y : ℤ, k * x - 5 * y + 7 = 0 ∧ k ^ 2 * x - 5 * y + 1 = 0} = {-2, 3} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Let's prove the forward direction: if k is in the set, then k ∈ {-2, 3}
      rintro ⟨x, y, h1, h2⟩
      have h3 : k * x * (k - 1) = 6 := by
        nlinarith
      have h4 : k * x * (k - 1) = 6 := h3
      have h6 : k - 1 ∣ 6 := by
        use k * x
        all_goals linarith
      have h8 : k - 1 ≤ 6 := by
        apply Int.le_of_dvd (by norm_num) h6
      have h9 : k - 1 ≥ -6 := by
        have h10 : (- (k - 1)) ∣ 6 := by
          exact Int.neg_dvd.2 h6
        have h11 : - (k - 1) ≤ 6 := by
          apply Int.le_of_dvd (by norm_num) h10
        omega
      have h10 : k ≤ 7 := by omega
      have h11 : k ≥ -5 := by omega
      interval_cases k <;> omega
    · -- Backward. If k in { -2, 3 } then it is in the set
      rintro (rfl | rfl)
      · -- Case k = -2
        use 1, 1
        all_goals norm_num
      · -- Case k = 3
        use 1, 2
        all_goals norm_num
  rw [h1]
  rw [Set.ncard_pair (by norm_num)]