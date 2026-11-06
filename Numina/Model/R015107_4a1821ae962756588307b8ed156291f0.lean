import Mathlib

theorem number_theory_13262 :
    Set.ncard {n : ℤ | ∃ k : ℤ, (3 * n + 4 : ℝ) / (n ^ 2 + n + 1) = k} = 3 := by
  have h1 : {n : ℤ | ∃ k : ℤ, (3 * n + 4 : ℝ) / (n ^ 2 + n + 1) = k} = {-1, 0, 3} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume h: ∃ k : ℤ, (3 * n + 4 : ℝ) / (n ^ 2 + n + 1) = k, prove n ∈ {-1, 0, 3}
      intro h
      rcases h with ⟨k, hk⟩
      have h2 : (n : ℝ) ^ 2 + (n : ℝ) + 1 > (0 : ℝ) := by
        nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n + 1 : ℝ))]
      have h3 : (3 * n + 4 : ℝ) = (k : ℝ) * ((n : ℝ) ^ 2 + (n : ℝ) + 1) := by
        field_simp at hk ⊢
        all_goals
          nlinarith
      have h4 : 3 * n + 4 = k * (n ^ 2 + n + 1) := by
        exact_mod_cast h3
      have h5 : n ^ 2 + n + 1 ∣ 3 * n + 4 := by
        use k
        all_goals
          linarith [h4]
      have h6 : n ^ 2 + n + 1 > 0 := by 
        nlinarith [sq_nonneg (n + 1), sq_nonneg (n)]
      have h7 : n ≤ 3 := by
        by_contra h
        push_neg at h
        have h9 : k ≤ 3 := by
          nlinarith [show k * (n ^ 2 + n + 1) = 3 * n + 4 from by linarith [h4], sq_nonneg (n), sq_nonneg (n + 1)]
        have h10 : k ≥ -3 := by
          nlinarith [show k * (n ^ 2 + n + 1) = 3 * n + 4 from by linarith [h4], sq_nonneg (n), sq_nonneg (n + 1)]
        interval_cases k <;> 
          nlinarith [sq_nonneg (n), sq_nonneg (n + 1)]
      have h9 : n ≥ -1 := by
        by_contra h
        push_neg at h
        have h9 : k ≤ 3 := by
          nlinarith [show k * (n ^ 2 + n + 1) = 3 * n + 4 from by linarith [h4], sq_nonneg (n), sq_nonneg (n + 1)]
        have h10 : k ≥ -3 := by
          nlinarith [show k * (n ^ 2 + n + 1) = 3 * n + 4 from by linarith [h4], sq_nonneg (n), sq_nonneg (n + 1)]
        interval_cases k <;> 
          nlinarith [sq_nonneg (n), sq_nonneg (n + 1)]
      interval_cases n <;> norm_num at *
      <;> omega
    · -- Assume n ∈ {-1, 0, 3}, prove ∃ k : ℤ, (3 * n + 4 : ℝ) / (n ^ 2 + n + 1) = k
      rintro (rfl | rfl | rfl)
      · -- n = -1
        use 1
        norm_num
      · -- n = 0
        use 4
        norm_num
      · -- n = 3
        use 1
        norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp