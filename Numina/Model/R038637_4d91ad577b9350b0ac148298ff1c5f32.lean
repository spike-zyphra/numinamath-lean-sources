import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_166004 (b : ℝ) :
  (∀ m : ℝ, ∃ x y, x^2 + 2 * y^2 = 3 ∧ y = m * x + b) ↔
  b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2) := by
  constructor
  · -- Forward direction: if ∀m, ∃(x,y) on the ellipse and line, then b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2)
    intro h
    have h1 : -Real.sqrt 6 / 2 ≤ b ∧ b ≤ Real.sqrt 6 / 2 := by
      have h2 := h 0
      rcases h2 with ⟨x, y, h_eq1, h_eq2⟩
      have hy : y = b := by
        linarith
      rw [hy] at h_eq1
      have h3 : x ^ 2 = 3 - 2 * b ^ 2 := by
        linarith
      have h4 : 3 - 2 * b ^ 2 ≥ 0 := by
        nlinarith [sq_nonneg x]
      constructor
      · -- Show that -Real.sqrt 6 / 2 ≤ b
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg b, Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num)]
      · -- Show that b ≤ Real.sqrt 6 / 2
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg b, Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num)]
    exact h1
  · -- Backward direction: if b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2), then ∀m, ∃x y, x^2 + 2y^2 = 3 ∧ y = mx + b
    rintro (⟨hb1, hb2⟩)
    intro m
    have h1 : b ^ 2 ≤ (3 / 2 : ℝ) := by
      have h1 : -Real.sqrt 6 / 2 ≤ b := by
        linarith [hb1]
      have h2 : b ≤ Real.sqrt 6 / 2 := by
        linarith [hb2]
      have h3 : (Real.sqrt 6 / 2 : ℝ) ^ 2 = (3 / 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      nlinarith [sq_nonneg b, h3, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    use (-2 * m * b + Real.sqrt (6 * m^2 - 2 * b^2 + 3)) / (1 + 2 * m^2)
    use m * ((-2 * m * b + Real.sqrt (6 * m^2 - 2 * b^2 + 3)) / (1 + 2 * m^2)) + b
    constructor
    · -- Check that x^2 + 2 * y^2 = 3
      field_simp
      nlinarith [Real.sqrt_nonneg (6 * m^2 - 2 * b^2 + 3), Real.sq_sqrt (show (0 : ℝ) ≤ (6 * m^2 - 2 * b^2 + 3 : ℝ) by nlinarith [sq_nonneg (m), h1, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]), sq_nonneg (m * b), sq_nonneg (Real.sqrt (6 * m^2 - 2 * b^2 + 3)), sq_nonneg (m), sq_nonneg (b)]
    · -- Check that y = m * x + b
      ring