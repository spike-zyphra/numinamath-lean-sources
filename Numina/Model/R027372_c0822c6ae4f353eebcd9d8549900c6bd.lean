import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_180898 (b : ℝ) :
  (∀ m : ℝ, ∃ x y, x^2 + 2*y^2 = 3 ∧ y = m*x + b) ↔
  b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2) := by
  constructor
  · -- Forward direction: Assume that for all $m$, $M \cap N \neq \varnothing$, prove $b \in Icc (-sqrt 6 / 2) (sqrt 6 / 2)$.
    intro h
    have h1 : -Real.sqrt 6 / 2 ≤ b := by
      by_contra h2
      push_neg at h2
      have h3 : b < -Real.sqrt 6 / 2 := by linarith
      have h4 : b ^ 2 > 3 / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      have h5 := h 0
      rcases h5 with ⟨x, y, h_eq1, h_eq2⟩
      have h6 : y = b := by linarith
      rw [h6] at h_eq1
      nlinarith [sq_nonneg x, h4]
    have h2 : b ≤ Real.sqrt 6 / 2 := by
      by_contra h3
      push_neg at h3
      have h4 : b > Real.sqrt 6 / 2 := by linarith
      have h5 : b ^ 2 > 3 / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      have h5 := h 0
      rcases h5 with ⟨x, y, h_eq1, h_eq2⟩
      have h6 : y = b := by linarith
      rw [h6] at h_eq1
      nlinarith [sq_nonneg x, h5]
    exact ⟨h1, h2⟩
  · -- Backward direction: Assume $b \in Icc (-sqrt 6 / 2) (sqrt 6 / 2)$, prove $∀ m : ℝ, ∃ x y, x^2 + 2*y^2 = 3 ∧ y = m*x + b$.
    rintro ⟨hb1, hb2⟩
    intro m
    have h1 : b ^ 2 ≤ 3 / 2 := by
      have h4 : -Real.sqrt 6 / 2 ≤ b := hb1
      have h5 : b ≤ Real.sqrt 6 / 2 := hb2
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (b ^ 2 - 3 / 2), sq_nonneg (b), Real.sqrt_nonneg 6]
    use ( -2 * m * b + Real.sqrt (3 - 2 * b ^ 2 + 6 * m ^ 2) ) / (1 + 2 * m ^ 2 )
    use m * (( -2 * m * b + Real.sqrt (3 - 2 * b ^ 2 + 6 * m ^ 2) ) / (1 + 2 * m ^ 2 )) + b
    constructor
    · -- Show that x^2 + 2*y^2 = 3
      field_simp
      nlinarith [ Real.sqrt_nonneg (3 - 2 * b ^ 2 + 6 * m ^ 2), Real.sq_sqrt (show 0 ≤ (3 - 2 * b ^ 2 + 6 * m ^ 2 : ℝ) by nlinarith ) ]
    · -- Show that y = m * x + b
      linarith