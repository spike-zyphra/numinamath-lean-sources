import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_180106 (x : ℝ) :
  (x^4 - 2 * x^2 - 8) / (x^2 + 2 * x + 1) < 0 ↔
  (x ∈ Ioo (-2) (-1) ∪ Ioo (-1) 2) := by
  have h1 : x^4 - 2 * x^2 - 8 = (x ^ 2 - 4) * (x^2 + 2) := by
    nlinarith
  have h4 : x^2 + 2 * x + 1 = (x + 1)^2 := by 
    ring
  have h7 : (x^4 - 2 * x^2 - 8) / (x^2 + 2 * x + 1) = ((x ^ 2 - 4) * (x^2 + 2) / ((x + 1)^2)) := by
    rw [h1, h4]
  rw [h7]
  constructor
  · -- Assume $\frac{(x ^ 2 - 4) * (x ^ 2 + 2)}{(x + 1) ^ 2} < 0$
    intro h
    have h8 : (x ^ 2 - 4) * (x^2 + 2) / ((x + 1) ^ 2) < 0 := h
    have h11 : (x ^ 2 - 4) * (x^2 + 2) < 0 := by 
      by_contra h12
      push_neg at h12
      have h13 : (x ^ 2 - 4) * (x^2 + 2) ≥ 0 := by linarith
      have h14 : (x + 1) ^ 2 > 0 := by 
        by_contra h15 
        push_neg at h15 
        have h16 : (x + 1) ^ 2 = 0 := by nlinarith 
        have h17 : x + 1 = 0 := by 
          apply pow_eq_zero 
          exact h16 
        have h18 : x = -1 := by linarith 
        rw [h18] at h8 
        norm_num at h8 
      have h14a : ( (x ^ 2 - 4) * (x^2 + 2) ) / ((x + 1) ^ 2 ) ≥ 0 := by 
        apply div_nonneg 
        linarith 
        nlinarith 
      linarith
    have h18 : (x + 1) ^ 2 > 0 := by 
      by_contra h19 
      push_neg at h19 
      have h20 : (x + 1) ^ 2 = 0 := by nlinarith 
      have h21 : x + 1 = 0 := by 
        apply pow_eq_zero 
        exact h20 
      have h22 : x = -1 := by linarith 
      rw [h22] at h8 
      norm_num at h8 
    have h8_a : x ^ 2 - 4 < 0 := by
      nlinarith [show x^2 + 2 > 0 by nlinarith, sq_nonneg (x^2 - 4)]
    have h22 : -2 < x := by 
      nlinarith 
    have h25 : x < 2 := by 
      nlinarith 
    have h89 : x ≠ -1 := by 
      by_contra h90 
      have h91 : x = -1 := by linarith 
      rw [h91] at h8 
      norm_num at h8 
    by_cases h26 : x < -1 
    · -- Case where x < -1, then x \in (-2, -1)
      left 
      constructor <;> linarith 
    · -- x ≥ -1, so x > -1 
      have h27 : x > -1 := by 
        by_contra h28 
        push_neg at h28 
        have h29 : x = -1 := by 
          nlinarith 
        contradiction 
      right 
      constructor <;> linarith
  · -- Assume the right side
    rintro (h | h)
    · -- Case where x ∈ (-2, -1)
      rcases h with ⟨h1_a, h2_b⟩
      have h5 : x ^ 2 - 4 < 0 := by 
        nlinarith 
      have h6 : (x + 1) ^ 2 > 0 := by 
        nlinarith 
      have h7_a : (x ^ 2 - 4) * (x^2 + 2) < 0 := by 
        nlinarith 
      have h8_b : ( (x ^ 2 - 4) * (x^2 + 2) ) / ((x + 1) ^ 2) < 0 := by 
        apply div_neg_of_neg_of_pos 
        linarith 
        linarith 
      linarith
    · -- Case where x ∈ (-1, 2)
      rcases h with ⟨h3, h4⟩ 
      have h5 : x ^ 2 - 4 < 0 := by 
        nlinarith 
      have h6 : (x + 1) ^ 2 > 0 := by 
        nlinarith 
      have h7_a : (x ^ 2 - 4) * (x^2 + 2) < 0 := by 
        nlinarith 
      have h8_b : ( (x ^ 2 - 4) * (x^2 + 2) ) / ((x + 1) ^ 2) < 0 := by 
        apply div_neg_of_neg_of_pos 
        linarith 
        linarith 
      linarith