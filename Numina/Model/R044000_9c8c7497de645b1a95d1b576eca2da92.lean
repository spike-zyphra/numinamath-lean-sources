import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_30991 (a b c : ℝ) (h : ∀ x ∈ Icc (-1) 1, |a * x ^ 2 + b * x + c| ≤ 1) :
    |c| ≤ 1 ∧ |a + c| ≤ 1 ∧ a ^ 2 + b ^ 2 + c ^ 2 ≤ 5 := by
  have h1 := h 1 (by norm_num)
  have h2 := h (-1 : ℝ) (by norm_num)
  have h3 := h (0 : ℝ) (by norm_num)
  have h4 := h (1 / 2 : ℝ) (by norm_num)
  have h5 := h (-1 / 2 : ℝ) (by norm_num)
  have h11 : -1 ≤ a + b + c := by
    linarith [abs_le.mp h1]
  have h12 : a + b + c ≤ 1 := by
    linarith [abs_le.mp h1]

  have h21 : -1 ≤ a - b + c := by
    linarith [abs_le.mp h2]
  have h22 : a - b + c ≤ 1 := by
    linarith [abs_le.mp h2]

  have h31 : -1 ≤ c := by 
    linarith [abs_le.mp h3]
  have h32 : c ≤ 1 := by 
    linarith [abs_le.mp h3]

  have h41 : -1 ≤ a * (1 / 2 : ℝ) ^ 2 + b * (1 / 2 : ℝ) + c := by
    linarith [abs_le.mp h4]
  have h42 : a * (1 / 2 : ℝ) ^ 2 + b * (1 / 2 : ℝ) + c ≤ 1 := by
    linarith [abs_le.mp h4]

  have h51 : -1 ≤ a * (-1 / 2 : ℝ) ^ 2 + b * (-1 / 2 : ℝ) + c := by
    linarith [abs_le.mp h5]
  have h52 : a * (-1 / 2 : ℝ) ^ 2 + b * (-1 / 2 : ℝ) + c ≤ 1 := by
    linarith [abs_le.mp h5]

  have h6 : |c| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · linarith [h32]
    · linarith [h31]

  have h7 : |a + c| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · -- Show that a + c ≤ 1
      nlinarith
    · -- Show that -1 ≤ a + c
      nlinarith

  have h8 : a ^ 2 + b ^ 2 + c ^ 2 ≤ 5 := by
    nlinarith [sq_nonneg (a + c), sq_nonneg (b), sq_nonneg (a - c), sq_nonneg (a + 2 * b), sq_nonneg (2 * a + 2 * c), sq_nonneg (b - 1), sq_nonneg (b + 1), sq_nonneg (a - 2), sq_nonneg (a + 2)]
  
  constructor
  · exact h6
  constructor
  · exact h7
  · exact h8