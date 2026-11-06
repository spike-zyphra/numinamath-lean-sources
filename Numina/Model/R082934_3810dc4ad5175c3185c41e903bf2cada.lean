import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_189940 (x : ℝ) :
  (x^2 + 3) > 0 ∧ (4 * x^2 - 16 * x) ≠ 0 ∧
  logb 5 (x^2 + 3) / (4 * x^2 - 16 * x) < 0 ↔ x ∈ Ioo 0 4 := by
    constructor
    · -- Assume left side holds
      intro h
      rcases h with ⟨h1, h2, h3⟩
      have h4 : logb 5 (x^2 + 3) > 0 := by
        have h5 : x^2 + 3 > 1 := by 
          nlinarith [sq_nonneg x]
        have h6 : logb 5 (x^2 + 3) > 0 := by 
          apply logb_pos
          all_goals nlinarith
        exact h6
      have h5 : 4 * x^2 - 16 * x < 0 := by 
        apply div_neg_iff.mp at h3
        cases h3 with
        | inl h6 =>
          linarith
        | inr h7 =>
          linarith [h4]
      have h6 : 0 < x := by 
        have h7 : 4 * x^2 - 16 * x < 0 := h5
        have h7' : x * (x - 4) < 0 := by nlinarith
        cases mul_neg_iff.mp h7' with
        | inl h8 =>
          linarith
        | inr h9 =>
          linarith
      have h7 : x < 4 := by 
        have h7 : 4 * x^2 - 16 * x < 0 := h5
        have h7' : x * (x - 4) < 0 := by nlinarith
        cases mul_neg_iff.mp h7' with
        | inl h8 =>
          linarith
        | inr h9 =>
          linarith
      exact ⟨h6, h7⟩
    · -- Assume x ∈ (0, 4)
      intro h
      rw [mem_Ioo] at h
      obtain ⟨h1, h2⟩ := h
      constructor
      · -- Show x^2 + 3 > 0
        nlinarith [sq_nonneg x]
      constructor
      · -- Show 4 * x^2 - 16 * x ≠ 0
        by_contra h3
        have h4 : x * (x - 4) = 0 := by 
          nlinarith
        cases (mul_eq_zero.mp h4) with
        | inl h5 =>
          linarith
        | inr h6 =>
          linarith
      · -- Show logb 5 (x^2 + 3) / (4 * x^2 - 16 * x) < 0
        have h3 : logb 5 (x^2 + 3) > 0 := by 
          have h4 : x^2 + 3 > 1 := by
            nlinarith [sq_nonneg x]
          apply logb_pos 
          all_goals nlinarith
        have h4 : 4 * x^2 - 16 * x < 0 := by 
          have h5 : x * (x - 4) < 0 := by 
            apply mul_neg_of_pos_of_neg 
            <;> linarith 
          nlinarith
        apply div_neg_of_pos_of_neg 
        all_goals linarith