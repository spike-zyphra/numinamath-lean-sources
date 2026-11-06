import Mathlib

theorem algebra_158906 {a b c : ℚ} (h : (a + b + c) * (a + b - c) = 4 * c ^ 2) : a + b = 0 := by 
  have h1 : (a + b) ^ 2 = 5 * c ^ 2 := by 
    nlinarith
  by_cases h2 : c = 0
  · -- If c = 0, then from h1 we have (a + b)^2 = 0.
    rw [h2] at h1
    have h3 : (a + b) ^ 2 = 0 := by
      linarith
    have h4 : a + b = 0 := by
      simp at h3 ⊢
      exact h3
    exact h4
  · -- Assume c ≠ 0
    have h3 : (a + b) ^ 2 = 5 * c ^ 2 := h1
    have h4 : a + b = 0 := by
      by_contra h5
      have h6 : (a + b) ^ 2 = 5 * c ^ 2 := h1
      have h7 : c ≠ 0 := h2
      have h8 : ((a + b) / c) ^ 2 = 5 := by
        have h10 : c ≠ 0 := h2
        field_simp [h10] at *
        nlinarith
      have h9 : ((a + b) / c) ^ 2 - 5 = 0 := by
        linarith
      have h10 : ((a + b) / c : ℚ) ^ 2 - 5 = 0 := by 
        linarith
      have h11 : ((a + b) / c : ℝ) ^ 2 - (5 : ℝ) = 0 := by
        exact_mod_cast h10
      have h12 : ((a + b) / c : ℝ) ^ 2 - (5 : ℝ) = (( (a + b) / c : ℝ ) - Real.sqrt (5 : ℝ)) * (( (a + b) / c : ℝ ) + Real.sqrt (5 : ℝ)) := by
        ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        all_goals linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num : (5 : ℝ) > 0)]
      rw [h12] at h11
      cases (mul_eq_zero.mp h11) with
      | inl h8 =>
        have h9 : ((a + b) / c : ℝ) = Real.sqrt (5 : ℝ) := by linarith
        have h4 : Irrational (Real.sqrt (5 : ℝ)) := by
          native_decide
        have h5 : ¬ Irrational ((a + b) / c : ℝ) := by 
          simp
        have h6 : Irrational ((a + b) / c : ℝ) := by
          rw [h9]
          exact h4
        contradiction
      | inr h8 =>
        have h9 : ((a + b) / c : ℝ) = -Real.sqrt (5 : ℝ) := by linarith
        have h4 : Irrational (Real.sqrt (5 : ℝ)) := by
          native_decide
        have h5 : ¬ Irrational ((a + b) / c : ℝ) := by 
          simp
        have h6 : Irrational ((a + b) / c : ℝ) := by
          rw [h9]
          have h7 : Irrational (-Real.sqrt (5 : ℝ)) := by
            apply Irrational.neg
            exact h4
          exact h7
        contradiction
    exact h4