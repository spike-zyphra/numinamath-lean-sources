import Mathlib

theorem number_theory_269034 :
    Set.ncard {n : ℤ | Odd n ∧ (17 / 4 : ℝ) < n ∧ n < (35 / 2 : ℝ)} = 7 := by
  have h1 : {n : ℤ | Odd n ∧ (17 / 4 : ℝ) < n ∧ n < (35 / 2 : ℝ)} = {5, 7, 9, 11, 13, 15, 17} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n is in left side, prove it's in right
      intro h
      rcases h with ⟨h_odd, h1, h2⟩
      have h3 : n > 4 := by
        by_contra h'
        push_neg at h'
        have h4 : n ≤ 4 := by linarith
        have h5 : (n : ℝ) ≤ (4 : ℝ) := by exact_mod_cast h4
        nlinarith
      have h4 : n < 18 := by
        by_contra h'
        push_neg at h'
        have h5 : n ≥ 18 := by linarith
        have h6 : (n : ℝ) ≥ (18 : ℝ) := by exact_mod_cast h5
        nlinarith
      interval_cases n <;> norm_num [Int.odd_iff] at h_odd ⊢ <;> tauto

    · -- Assume n is in right side, prove it's in left
      rintro (r | r | r | r | r | r | r)
      · -- n = 5
        rw [r]
        constructor
        · decide
        constructor
        · norm_num
        · norm_num
      · -- n = 7
        rw [r]
        constructor
        · decide
        constructor
        · norm_num
        · norm_num
      · -- n = 9
        rw [r]
        constructor
        · decide
        constructor
        · norm_num
        · norm_num
      · -- n = 11
        rw [r]
        constructor
        · decide
        constructor
        · norm_num
        · norm_num
      · -- n = 13
        rw [r]
        constructor
        · decide
        constructor
        · norm_num
        · norm_num
      · -- n = 15
        rw [r]
        constructor
        · decide
        constructor
        · norm_num
        · norm_num
      · -- n = 17
        rw [r]
        constructor
        · decide
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> norm_num