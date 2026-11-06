import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_190255 (x : ℝ) (hx : x^2 - 1 ≠ 0) :
    (0.2 : ℝ) ^ ((x^2 + 2) / (x^2 - 1)) > 25 ↔ x ∈ Ioo (-1) 0 ∪ Ioo 0 1 := by
  constructor
  · -- Assume (0.2 : ℝ) ^ ((x^2 + 2) / (x^2 - 1)) > 25, prove x ∈ Ioo (-1) 0 ∪ Ioo 0 1
    intro h
    have h1 : (0.2 : ℝ) ^ ((x^2 + 2) / (x^2 - 1)) > 25 := h
    have h2 : (x^2 + 2) / (x^2 - 1) < -2 := by
      by_contra h3
      push_neg at h3
      have h3' : (0.2 : ℝ) ^ ((x ^ 2 + 2) / (x ^ 2 - 1)) ≤ (0.2 : ℝ) ^ (-2 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_ge
        all_goals norm_num
        all_goals linarith
      have h4 : (0.2 : ℝ) ^ (-2 : ℝ) = 25 := by
        norm_num [Real.rpow_neg, Real.rpow_natCast, pow_two]
      have h5 : (0.2 : ℝ) ^ ((x ^ 2 + 2) / (x ^ 2 - 1)) ≤ (25 : ℝ) := by
        linarith [h3', h4]
      linarith [h5, h1]
    have h3 : (x^2 + 2) / (x^2 - 1) < -2 := h2
    have h4 : x^2 < 1 := by
      by_contra h5
      push_neg at h5
      by_cases h6 : x^2 - 1 > 0
      · -- If x^2 - 1 > 0, then x^2 > 1
        have : x^2 > 1 := by
          nlinarith
        have h8 : (x^2 + 2) / (x^2 - 1) ≥ -2 := by
          apply (le_div_iff₀ (by nlinarith)).mpr
          nlinarith [this, sq_nonneg (x ^ 2 - 1)]
        linarith
      · -- x^2 - 1 ≤ 0
        have : x^2 ≤ 1 := by
          nlinarith
        have h7 : x^2 = 1 := by
          by_cases h7' : x^2 < 1
          · -- x^2 < 1, so x^2 - 1 < 0
            have h71 : x^2 - 1 < 0 := by
              nlinarith
            have h70 : (x^2 + 2) / (x^2 - 1) < -2 := h2
            have : (x^2 + 2) / (x^2 - 1) = (x^2 + 2) / (x^2 - 1) := rfl
            -- For x^2 < 1: denominator neg, so multiply neg
            have : (x^2 + 2) >= -2 * (x^2 - 1) := by
              have : (x^2 + 2) / (x^2 - 1) >= -2 := by
                apply (le_div_iff_of_neg' (by nlinarith)).mpr
                nlinarith [this, sq_nonneg (x ^ 2 - 1)]
                all_goals nlinarith
              all_goals nlinarith
            nlinarith [this, sq_nonneg (x ^ 2 - 1)]
          · -- ¬(x^2 < 1) ∧ x^2 ≤ 1 → x^2 = 1
            have : x^2 = 1 := by
              linarith
            assumption
        have : x^2 - 1 = 0 := by
          nlinarith
        contradiction
    have h5 : x ^ 2 < 1 := h4
    have h51 : -1 < x := by nlinarith [sq_nonneg (x), sq_nonneg (x ^ 2 - 1)]
    have h52 : x < 1 := by nlinarith [sq_nonneg (x), sq_nonneg (x ^ 2 - 1)]
    have h7 : x ≠ 0 := by
      by_contra h8
      rw [h8] at h2
      norm_num at h2
      all_goals nlinarith [sq_nonneg (x), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2),
        sq_pos_of_pos (by norm_num : (0.2 : ℝ) > 0)]
    have h8 : x > 0 ∨ x < 0 := by
      by_contra h
      push_neg at h
      have h9 : x = 0 := by
        linarith
      contradiction
    cases h8 with
    | inl h8 =>
      have h9 : x ∈ Ioo 0 1 := ⟨by nlinarith, by nlinarith⟩
      simp [Set.mem_union, h9]
      all_goals try { tauto }
    | inr h8 =>
      have h9 : x ∈ Ioo (-1) 0 := ⟨by nlinarith, by nlinarith⟩
      simp [Set.mem_union, h9]
      all_goals try { tauto }
  · -- Assume x ∈ Ioo (-1) 0 ∪ Ioo 0 1, prove (0.2 : ℝ) ^ ((x^2 + 2) / (x^2 - 1)) > 25
    rintro (h | h)
    · -- Case x ∈ (-1, 0)
      rcases h with ⟨h1, h2⟩
      have h3 : x < 0 := by linarith
      have h4 : x ^ 2 < 1 := by nlinarith
      have h5 : (x ^ 2 + 2) / (x ^ 2 - 1) < -2 := by
        have h6 : x ^ 2 - 1 < 0 := by nlinarith
        apply (div_lt_iff_of_neg' (by nlinarith)).mpr
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 1)]
      have h6 : (0.2 : ℝ) ^ ((x ^ 2 + 2) / (x ^ 2 - 1)) > 25 := by
        have h7 : (0.2 : ℝ) ^ ((x ^ 2 + 2) / (x ^ 2 - 1)) > (0.2 : ℝ) ^ (-2 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_gt
          all_goals norm_num
          all_goals linarith
        have h8 : (0.2 : ℝ) ^ (-2 : ℝ) = 25 := by
          norm_num [Real.rpow_neg, Real.rpow_natCast, pow_two]
        linarith [h7, h8]
      linarith
    · -- Case x ∈ (0, 1)
      rcases h with ⟨h1, h2⟩
      have h3 : 0 < x := by linarith
      have h4 : x ^ 2 < 1 := by nlinarith
      have h5 : (x ^ 2 + 2) / (x ^ 2 - 1) < -2 := by
        have h6 : x ^ 2 - 1 < 0 := by nlinarith
        apply (div_lt_iff_of_neg' (by nlinarith)).mpr
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 1)]
      have h6 : (0.2 : ℝ) ^ ((x ^ 2 + 2) / (x ^ 2 - 1)) > 25 := by
        have h7 : (0.2 : ℝ) ^ ((x ^ 2 + 2) / (x ^ 2 - 1)) > (0.2 : ℝ) ^ (-2 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_gt
          all_goals norm_num
          all_goals linarith
        have h8 : (0.2 : ℝ) ^ (-2 : ℝ) = 25 := by
          norm_num [Real.rpow_neg, Real.rpow_natCast, pow_two]
        linarith [h7, h8]
      linarith