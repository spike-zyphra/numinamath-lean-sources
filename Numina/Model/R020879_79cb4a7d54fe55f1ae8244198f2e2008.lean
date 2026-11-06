import Mathlib

theorem number_theory_118204 (a : ℝ) (ha : ∃ q1 q2 : ℚ, a^18 = q1 ∧ a^11 = q2) :
    ∃ q : ℚ, a = q := by
  rcases ha with ⟨q1, q2, ha18, ha11⟩
  have h1 : a^18 = (q1 : ℝ) := by 
    exact_mod_cast ha18
  have h2 : a^11 = (q2 : ℝ) := by
    exact_mod_cast ha11
  by_cases h : a = (0 : ℝ)
  · -- if a =0, then clearly rational
    use (0 : ℚ)
    rw [h]
    all_goals norm_num
  · -- a ≠0
    have ha1 : a ≠ 0 := h
    -- derive the witness
    have h6 : a^18 = (q1 : ℝ) := h1
    have h7 : a^11 = (q2 : ℝ) := h2
    have h8 : a = ((a ^ 11) ^ 5) / ((a ^ 18) ^ 3) := by
      have h13 : a ^ 18 ≠ 0 := by
        by_contra h'
        have h9 : a ^ 18 = (0 : ℝ) := by
          linarith
        have h10 : (q1 : ℝ) = (0 : ℝ) := by 
          linarith [h9, h6]
        have h11 : (q1 : ℚ) = (0 : ℚ) := by
          exact_mod_cast h10
        have h12 : (q1 : ℝ) = (0 : ℝ) := by 
          exact_mod_cast h11
        have h13 : a ^ 18 = (0 : ℝ) := by
          linarith [h12, h6]
        have h14 : a = (0 : ℝ) := by
          have : a ^ 18 = (0 : ℝ) := h13
          have h15 : a = (0 : ℝ) := by
            have h18 : a ^ 18 = (0 : ℝ) := this
            have : a = 0 := by
              have h18 : a ^ 18 = (0 : ℝ) := h18
              simp at h18 ⊢
              <;> nlinarith [sq_nonneg (a ^ 1), sq_nonneg (a ^ 2), sq_nonneg (a ^ 3), sq_nonneg (a ^ 4), sq_nonneg (a ^ 5), sq_nonneg (a ^ 6), sq_nonneg (a ^ 7), sq_nonneg (a ^ 8), sq_nonneg (a ^ 9)]
            linarith
          linarith
        exfalso
        exact h (h14)
      field_simp [h13]
      <;> ring_nf
      <;> norm_num
      <;> nlinarith
    rw [h7, h6] at h8
    use (q2 ^ 5 / q1 ^ 3)
    rw [h8]
    all_goals norm_num