import Mathlib

theorem algebra_15931 : {n : ℕ | 0 < n ∧ (n : ℝ) ^ ((1 : ℝ) / 3) < 10}.encard = 999 := by
  have h1 : {n : ℕ | 0 < n ∧ (n : ℝ) ^ ((1 : ℝ) / 3) < 10} = Set.Icc 1 999 := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume n is in {n : ℕ | 0 < n ∧ (n : ℝ) ^ ((1 : ℝ) / 3) < 10}
      rintro ⟨hn_pos, h⟩
      have h2 : (n : ℝ) < (1000 : ℝ) := by
        by_contra h2
        push_neg at h2
        have h3 : (n : ℝ) ^ ((1 : ℝ) / 3) ≥ (10 : ℝ) := by
          have h4 : (n : ℝ) ≥ (1000 : ℝ) := by
            exact_mod_cast h2
          have h5 : (n : ℝ) ^ ((1 : ℝ) / 3) ≥ (1000 : ℝ) ^ ((1 : ℝ) / 3) := by
            apply Real.rpow_le_rpow
            all_goals
              linarith
          have h6 : (1000 : ℝ) ^ ((1 : ℝ) / 3) = (10 : ℝ) := by
            rw [show (1000 : ℝ) = (10 : ℝ) ^ (3 : ℝ) by norm_num]
            rw [← Real.rpow_mul]
            norm_num
            all_goals
              norm_num
          linarith [h5, h6]
        linarith
      have h7 : n < 1000 := by
        by_contra h2
        push_neg at h2
        have h8 : (n : ℝ) ≥ (1000 : ℝ) := by
          exact_mod_cast h2
        nlinarith
      have h8 : n ≤ 999 := by
        omega
      constructor
      · -- Show that 1 ≤ n
        omega
      · -- Show that n ≤ 999
        omega
    · -- Assume n ∈ Set.Icc 1 999
      rintro ⟨h1, h2⟩
      constructor
      · -- Show that 0 < n
        omega
      · -- Show that (n : ℝ) ^ (1 / 3) < 10
        have h3 : (n : ℝ) < (1000 : ℝ) := by
          have h2' : n ≤ 999 := by
            omega
          have h3' : (n : ℝ) ≤ (999 : ℝ) := by
            exact_mod_cast h2'
          linarith
        have h4 : (n : ℝ) ^ ((1 : ℝ) / 3) < (10 : ℝ) := by
          have h5 : (n : ℝ) < (1000 : ℝ) := h3
          have h6 : (n : ℝ) ^ ((1 : ℝ) / 3) < (1000 : ℝ) ^ ((1 : ℝ) / 3) := by
            apply Real.rpow_lt_rpow
            all_goals
              nlinarith
          have h7 : (1000 : ℝ) ^ ((1 : ℝ) / 3) = (10 : ℝ) := by
            rw [show (1000 : ℝ) = (10 : ℝ) ^ (3 : ℝ) by norm_num]
            rw [← Real.rpow_mul]
            norm_num
            all_goals
              norm_num
          linarith [h6, h7]
        linarith
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_eq_toFinset_card']
  <;> native_decide