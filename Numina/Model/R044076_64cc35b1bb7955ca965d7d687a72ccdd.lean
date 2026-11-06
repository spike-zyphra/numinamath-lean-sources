import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_170389 (m : ℝ) :
  (∀ x : ℝ, (x^2 - 8 * x + 20) / (m * x^2 + 2 * (m + 1) * x + 9 * m + 4) < 0) ↔
  m < -1 / 2 := by
  constructor
  · -- Assume that ∀ x, (x^2 - 8*x + 20) / (m*x^2 + ...) < 0, prove m < -1/2.
    intro h
    have h1 : ∀ x : ℝ, x^2 - 8*x + 20 > 0 := by
      intro x
      nlinarith [sq_nonneg (x - 4)]
    have h2 : ∀ x : ℝ, m * x^2 + 2 * (m + 1) * x + 9 * m + 4 < 0 := by
      intro x
      have h3 := h x
      have hx1 : x^2 - 8*x + 20 > 0 := h1 x
      apply div_neg_iff.mp at h3
      cases h3 with
      | inl h3l => nlinarith
      | inr h3r => nlinarith
    have h_m_neg : m < 0 := by 
      by_contra h5
      push_neg at h5
      have h6 := h2 1
      have h7 := h2 (-1)
      norm_num at h6 h7
      nlinarith
    by_contra h'
    push_neg at h'
    have h3_1 := h2 1
    norm_num at h3_1
    nlinarith
  · -- Assume m < -1/2, prove the inequality holds for all real x
    intro h -- h : m < -1/2
    intro x 
    have h1 : x^2 - 8*x + 20 > 0 := by
      nlinarith [sq_nonneg (x - 4)]
    have h4 : m * x^2 + 2 * (m + 1) * x + 9 * m + 4 < 0 := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x * m + (m + 1) / 2), sq_nonneg (x + 2), sq_nonneg (x * m + 1), sq_nonneg (x * 9 + 4), sq_nonneg (x * m + (m + 1)), sq_nonneg (x * m + 1), sq_pos_of_pos (show (0 : ℝ) < -m by linarith), sq_nonneg ((x) * (m)), sq_nonneg ((m) * (m))]
    apply div_neg_of_pos_of_neg 
    linarith 
    linarith