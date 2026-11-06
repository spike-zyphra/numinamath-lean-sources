import Mathlib

theorem number_theory_256043 : {n : ℕ | n > 0 ∧ (n : ℚ) / (n + 1) < 7 / 9}.encard = 3 := by
  have h1 : {n : ℕ | n > 0 ∧ (n : ℚ) / (n + 1) < 7 / 9} = {1, 2, 3} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h : n ∈ {n : ℕ | n > 0 ∧ (n : ℚ) / (n + 1) < 7 / 9}
      intro h
      rcases h with ⟨h_n_pos, h_ineq⟩
      have h2 : (n : ℚ) > 0 := by
        exact_mod_cast h_n_pos
      have h3 : (n : ℚ) / (n + 1) < 7 / 9 := h_ineq
      have h4 : (n : ℚ) < 3.5 := by
        have h5 : (n : ℚ) / (n + 1) < 7 / 9 := h3
        have h6 : (n : ℚ) * 9 < 7 * (n + 1) := by
          apply (div_lt_div_iff (by positivity) (by positivity)).mp at h5
          linarith
        nlinarith
      have h8 : n < 4 := by
        by_contra h
        push_neg at h
        have h9 : n ≥ 4 := by omega
        have h10 : (n : ℚ) ≥ 4 := by
          exact_mod_cast h9
        linarith
      interval_cases n <;> norm_num at *
    · -- Assume n ∈ {1, 2, 3}
      rintro (rfl | rfl | rfl)
      · -- Case n = 1
        constructor
        · norm_num -- 1 > 0
        · norm_num -- 1 / 2 < 7 / 9
      · -- Case n = 2
        constructor
        · norm_num -- 2 > 0
        · norm_num -- 2 / 3 < 7 / 9
      · -- Case n = 3
        constructor
        · norm_num -- 3 > 0
        · norm_num -- 3 / 4 < 7 / 9
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]