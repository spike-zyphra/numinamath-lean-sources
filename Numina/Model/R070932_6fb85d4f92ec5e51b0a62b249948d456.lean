import Mathlib

theorem algebra_278594 {f : ℝ → ℝ} (hf : ∀ x, f x = 10 ^ x) :
    ∀ x1 x2 : ℝ, x1 ≠ x2 → f (x1 + x2) = f x1 * f x2 ∧ (f x1 - f x2) / (x1 - x2) > 0 := by
  intro x1 x2 hneq
  constructor
  · -- Proof of property (1): f(x1 + x2) = f(x1) * f(x2)
    rw [hf, hf, hf]
    simp [Real.rpow_add]
    all_goals linarith
  · -- Proof of property (3): (f(x1) - f(x2)) / (x1 - x2) > 0
    rw [hf, hf]
    apply div_pos_iff.mpr
    have h3 : (10 : ℝ) ^ x1 - (10 : ℝ) ^ x2 > 0 ↔ x1 > x2 := by
      constructor
      · -- Assume (10 : ℝ) ^ x1 - (10 : ℝ) ^ x2 > 0, prove x1 > x2
        intro h
        by_contra h4
        push_neg at h4
        have h5 : x1 ≤ x2 := by linarith
        have h6 : (10 : ℝ) ^ x1 ≤ (10 : ℝ) ^ x2 := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num) h5
        linarith
      · -- Assume x1 > x2, prove (10 : ℝ) ^ x1 - (10 : ℝ) ^ x2 > 0
        intro h
        have h7 : (10 : ℝ) ^ x1 > (10 : ℝ) ^ x2 := by
          apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h
        linarith
    -- Show that (10 ^ x1 - 10 ^ x2) * (x1 - x2) > 0
    have h4 : ((10 : ℝ) ^ x1 - (10 : ℝ) ^ x2) * (x1 - x2) > 0 := by
      by_cases h5 : x1 > x2
      · -- If x1 > x2
        have h6 : (10 : ℝ) ^ x1 - (10 : ℝ) ^ x2 > 0 := by linarith [h3.mpr h5]
        have h7 : x1 - x2 > 0 := by linarith
        have h8 : ((10 : ℝ) ^ x1 - (10 : ℝ) ^ x2) * (x1 - x2) > 0 := mul_pos h6 h7
        exact h8
      · -- Case x1 ≤ x2
        have h5 : x1 < x2 := by
          by_contra h6
          push_neg at h6
          have h7 : x1 ≥ x2 := by linarith
          have h8 : x1 > x2 := by
            by_contra h9
            push_neg at h9
            have h10 : x1 = x2 := by linarith
            exfalso
            exact hneq h10
          linarith
        have h6 : (10 : ℝ) ^ x1 - (10 : ℝ) ^ x2 < 0 := by
          have h7 : (10 : ℝ) ^ x1 < (10 : ℝ) ^ x2 := by
            apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h5
          linarith
        have h8 : x1 - x2 < 0 := by linarith
        have h9 : ((10 : ℝ) ^ x1 - (10 : ℝ) ^ x2) * (x1 - x2) > 0 := mul_pos_of_neg_of_neg h6 h8
        exact h9
    -- From (f(x1) - f(x2)) * (x1 - x2) > 0 to division via field switch
    have hneq2 : x1 - x2 ≠ 0 := by
      intro h
      apply hneq
      linarith
    cases mul_pos_iff.mp h4 with
    | inl h5 => 
      apply Or.inl
      all_goals
        field_simp [hneq2] at h5 ⊢
        all_goals linarith
    | inr h6 => 
      apply Or.inr
      all_goals
        field_simp [hneq2] at h6 ⊢
        all_goals linarith