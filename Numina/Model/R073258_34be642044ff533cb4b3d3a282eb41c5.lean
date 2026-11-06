import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_603128 (x : ℝ) :
  abs (x / (x - 2)) > x / (2 - x) ↔ x < 0 ∨ x > 2 := by
  constructor
  · -- Forward implication: abs (x / (x - 2)) > x / (2 - x) → x < 0 ∨ x > 2
    intro h
    have h1 : x - 2 ≠ 0 := by
      by_contra h2
      have h3 : x = 2 := by linarith
      rw [h3] at h
      norm_num at h
    have h2 : x / (2 - x) = - (x / (x - 2)) := by
      field_simp [(show x - 2 ≠ 0 by assumption), (show (2 - x) ≠ 0 by
        intro h3
        apply h1
        linarith
      )]
      <;> ring
    rw [h2] at h
    cases le_or_lt 0 (x / (x - 2)) with
    | inl h_nonneg =>
      rw [abs_of_nonneg h_nonneg] at h
      have h3 : x / (x - 2) > 0 := by nlinarith
      have h4 : (x > 0 ∧ x - 2 > 0) ∨ (x < 0 ∧ x - 2 < 0) := by 
        apply div_pos_iff.mp at h3
        exact h3
      cases h4 with
      | inl h5 =>
        right
        linarith
      | inr h6 =>
        left
        linarith
    | inr h_neg =>
      rw [abs_of_neg h_neg] at h
      have h3 : x / (x - 2) > 0 := by nlinarith
      have h4 : (x > 0 ∧ x - 2 > 0) ∨ (x < 0 ∧ x - 2 < 0) := by 
        apply div_pos_iff.mp at h3
        exact h3
      cases h4 with
      | inl h5 =>
        right
        linarith
      | inr h6 =>
        left
        linarith
  · -- Reverse implication: x < 0 ∨ x > 2 → abs (x / (x - 2)) > x / (2 - x)
    intro h
    cases h with
    | inl h1 =>
      have h2 : x - 2 ≠ 0 := by
        by_contra h3
        have : x = 2 := by linarith
        nlinarith
      have h3 : x / (x - 2) > 0 := by
        apply div_pos_of_neg_of_neg
        <;> nlinarith
      have h4 : abs (x / (x - 2)) = x / (x - 2) := by
        rw [abs_of_pos h3]
      have h5 : x / (2 - x) = - (x / (x - 2)) := by
        field_simp [(show x - 2 ≠ 0 by assumption), (show (2 - x) ≠ 0 by
          intro h3
          have h4 : x = 2 := by linarith
          nlinarith
        )]
        <;> ring
      rw [h4, h5]
      linarith
    | inr h2 =>
      have h3 : x - 2 ≠ 0 := by
        by_contra h4
        have : x = 2 := by linarith
        nlinarith
      have h4 : x / (x - 2) > 0 := by
        apply div_pos
        all_goals nlinarith
      have h5 : abs (x / (x - 2)) = x / (x - 2) := by
        rw [abs_of_pos h4]
      have h6 : x / (2 - x) = - (x / (x - 2)) := by
        field_simp [(show x - 2 ≠ 0 by assumption), (show (2 - x) ≠ 0 by
          intro h3
          have h4 : x = 2 := by linarith
          nlinarith
        )]
        <;> ring
      rw [h5, h6]
      linarith