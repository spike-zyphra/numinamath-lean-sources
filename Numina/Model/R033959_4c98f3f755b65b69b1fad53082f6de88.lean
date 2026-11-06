import Mathlib

theorem algebra_625 : {x : ℤ | x ≥ 0 ∧ ∃ k : ℤ, x * (x + 1) = (k - 2) * (k + 2)}.encard = 2 := by
  have h1 : {x : ℤ | x ≥ 0 ∧ ∃ k : ℤ, x * (x + 1) = (k - 2) * (k + 2)} = {0, 3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x in the set, prove x in {0, 3}
      intro h
      rcases h with ⟨hxge, ⟨k, hk⟩⟩
      have h2 : (2 * k - (2 * x + 1)) * (2 * k + (2 * x + 1)) = 15 := by
        nlinarith
      have h3 : (2 * k - (2 * x + 1)) ∣ 15 := by
        use (2 * k + (2 * x + 1))
        all_goals linarith
      have h4 : (2 * k - (2 * x + 1)) ≤ 15 := by
        apply Int.le_of_dvd (show 0 < (15 : ℤ) by norm_num) h3
      have h5 : (2 * k - (2 * x + 1)) ≥ -15 := by
        have h6 : (- (2 * k - (2 * x + 1))) ∣ 15 := by
          exact Int.neg_dvd.2 h3
        have h7 : - (2 * k - (2 * x + 1)) ≤ 15 := by
          apply Int.le_of_dvd (show 0 < (15 : ℤ) by norm_num) h6
        omega
      interval_cases h : 2 * k - (2 * x + 1) <;> omega
    · -- Show if x in {0, 3}, then in the set
      rintro (rfl | rfl)
      · -- x = 0
        constructor
        · norm_num
        · use -2
          all_goals norm_num
      · -- x = 3
        constructor
        · norm_num
        · use -4
          all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_pair]
  all_goals norm_num