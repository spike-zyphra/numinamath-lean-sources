import Mathlib

theorem algebra_17105 : {m : ℤ | m ≠ 0 ∧ (1 / |m| : ℝ) ≥ 1 / 8}.encard = 16 := by 
  have h1 : {m : ℤ | m ≠ 0 ∧ (1 / |m| : ℝ) ≥ 1 / 8} = {-8, -7, -6, -5, -4, -3, -2, -1, 1, 2, 3, 4, 5, 6, 7, 8} := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume m is in the left side, show it's in the right
      intro h
      rcases h with ⟨hmne0, h1⟩
      have h2 : m ≠ 0 := hmne0
      have h3 : (1 / |m| : ℝ) ≥ 1 / 8 := h1
      have h4 : (|m| : ℝ) > 0 := by
        have h5 : |m| > 0 := by
          cases' abs_cases m with h h
          · -- m ≥ 0, so |m| = m
            omega
          · -- m < 0, so |m| = -m
            omega
        exact_mod_cast h5
      have h3' : (1 : ℝ) ≥ (1 / 8) * (|m| : ℝ) := by
        have h7 : (1 / |m| : ℝ) ≥ (1 / 8 : ℝ) := h3
        have h8 : (0 : ℝ) < (|m| : ℝ) := by
          have h5 : (|m| : ℝ) > 0 := h4
          linarith
        have h10 : (1 / |m| : ℝ) * (|m| : ℝ) ≥ (1 / 8 : ℝ) * (|m| : ℝ) := by
          apply mul_le_mul_of_nonneg_right h7
          linarith
        have h11 : (1 / |m| : ℝ) * (|m| : ℝ) = 1 := by
          field_simp [show (|m| : ℝ) ≠ 0 by
            by_contra h0
            have : (|m| : ℝ) = 0 := by linarith
            have h9 : (|m| : ℝ) > 0 := h4
            linarith
          ]
        linarith [h11, h10]
      have h9 : (|m| : ℝ) ≤ 8 := by
        nlinarith
      have h10 : |m| ≤ 8 := by
        exact_mod_cast h9
      -- From abs m ≤ 8 and m ≠ 0, deduce m is in the right side
      have h11 : m ≤ 8 := by 
        linarith [abs_le.mp h10]
      have h12 : -8 ≤ m := by 
        linarith [abs_le.mp h10]
      interval_cases m <;> norm_num at hmne0 h1 ⊢ <;> tauto
    · -- Assume m is in the right side, show it's in the left
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        constructor
        · -- Show m ≠ 0
          norm_num
        · -- Show 1 / |m| ≥ 1 / 8
          norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals try { linarith }