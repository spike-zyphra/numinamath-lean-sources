import Mathlib

theorem inequalities_290899 : {n : ℕ | n > 0 ∧ (1 / (n + 1 : ℝ)) > 4 / 29}.encard = 6 := by
  have h1 : {n : ℕ | n > 0 ∧ (1 / (n + 1 : ℝ)) > 4 / 29} = {1, 2, 3, 4, 5, 6} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h: n > 0 ∧ 1 / (↑n + 1) > 4 / 29, prove n ∈ {1, 2, 3, 4, 5, 6}
      intro h
      rcases h with ⟨hn1, hn2⟩
      have h2 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast hn1
      have h5 : (n : ℝ) < (25 / 4 : ℝ) := by 
        have h6 : (n + 1 : ℝ) > (0 : ℝ) := by
          have hn7 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast hn1
          nlinarith
        have h8 : (1 / (n + 1 : ℝ)) > (4 / 29 : ℝ) := by 
          simpa using hn2
        have h6 : (n + 1 : ℝ) > (0 : ℝ) := by
          have hn7 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast hn1
          nlinarith
        have h9 : (29 : ℝ) > (0 : ℝ) := by norm_num
        have h11 : (1 / (n + 1) : ℝ) > (4 / 29 : ℝ) := by
          simpa using hn2
        have h12 : (29 : ℝ) > (4 * (n + 1) : ℝ) := by
          have h13 : (1 / (n + 1) : ℝ) > (4 / 29 : ℝ) := h11
          have h14 : (n + 1 : ℝ) > (0 : ℝ) := h6
          have h15 : (29 : ℝ) > (0 : ℝ) := by norm_num
          have h16 : (1 / (n + 1) : ℝ) * ((n + 1) * 29) > (4 / (29 : ℝ)) * ((n + 1) * (29 : ℝ)) := by
            apply mul_lt_mul_of_pos_right h13
            all_goals
              positivity
          have h17 : (1 / (n + 1) : ℝ) * ((n + 1) * 29) = 29 := by
            field_simp [show (n + 1 : ℝ) ≠ 0 by linarith]
            <;> nlinarith
          have h18 : (4 / (29 : ℝ)) * ((n + 1) * (29 : ℝ)) = (4 * (n + 1) : ℝ) := by
            field_simp [show (29 : ℝ) ≠ 0 by norm_num]
            <;> ring
          linarith [h17, h18, h16]
        nlinarith
      have h6 : n < 7 := by 
        by_contra h7
        push_neg at h7
        have h8 : n ≥ 7 := by omega
        have h9 : (n : ℝ) ≥ (7 : ℝ) := by exact_mod_cast h8
        nlinarith
      have h7 : n > 0 := hn1
      have h8 : n ≤ 6 := by omega
      omega
    · -- Assume n ∈ {1, 2, 3, 4, 5, 6}, prove n > 0 ∧ 1 / (↑n + 1) > 4 / 29
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 1
        constructor
        · norm_num
        · norm_num
      · -- n = 2
        constructor
        · norm_num
        · norm_num
      · -- n = 3
        constructor
        · norm_num
        · norm_num
      · -- n = 4
        constructor
        · norm_num
        · norm_num
      · -- n = 5
        constructor
        · norm_num
        · norm_num
      · -- n = 6
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> norm_num