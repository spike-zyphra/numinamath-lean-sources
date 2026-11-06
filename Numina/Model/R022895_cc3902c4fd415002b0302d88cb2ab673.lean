import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10576 {b : ℝ} :
  (∀ m : ℝ, ∃ x y : ℝ, x^2 + 2*y^2 = 3 ∧ y = m*x + b) ↔
  b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2) := by
  constructor
  · -- Assume that for all m, there exists (x, y) intersection point
    intro h
    have h1 : -sqrt 6 / 2 ≤ b := by
      have h2 := h 0
      rcases h2 with ⟨x, y, h_eq1, h_eq2⟩
      have h3 : x ^ 2 + 2 * y ^ 2 = 3 := h_eq1
      have h4 : y = b := by linarith
      rw [h4] at h3
      have h5 : 3 - 2 * b ^ 2 ≥ 0 := by nlinarith [sq_nonneg x]
      have h6 : b ^ 2 ≤ 3 / 2 := by nlinarith
      have h7 : sqrt 6 ^ 2 = 6 := by
        rw [Real.sq_sqrt]
        all_goals linarith
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (6 : ℝ) by linarith), h6]
    have h2 : b ≤ sqrt 6 / 2 := by
      have h2 := h 0
      rcases h2 with ⟨x, y, h_eq1, h_eq2⟩
      have h3 : x ^ 2 + 2 * y ^ 2 = 3 := h_eq1
      have h4 : y = b := by linarith
      rw [h4] at h3
      have h5 : 3 - 2 * b ^ 2 ≥ 0 := by nlinarith [sq_nonneg x]
      have h6 : b ^ 2 ≤ 3 / 2 := by nlinarith
      have h7 : sqrt 6 ^ 2 = 6 := by
        rw [Real.sq_sqrt]
        all_goals linarith
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (6 : ℝ) by linarith), h6]
    exact ⟨h1, h2⟩
  · -- Assume b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2)
    rintro ⟨hb1, hb2⟩
    intro m
    have h1 : b ^ 2 ≤ 3 / 2 := by
      have h2 : -sqrt 6 / 2 ≤ b := by
        linarith [hb1]
      have h3 : sqrt 6 / 2 ≥ b := by
        linarith [hb2]
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), sq_nonneg b]
    use (-2 * m * b + Real.sqrt (3 - 2 * b ^ 2 + 6 * m ^ 2)) / (1 + 2 * m ^ 2), 
        m * ((-2 * m * b + Real.sqrt (3 - 2 * b ^ 2 + 6 * m ^ 2)) / (1 + 2 * m ^ 2)) + b
    constructor
    · -- Show that (x, y) ∈ M
      field_simp
      nlinarith [Real.sqrt_nonneg (3 - 2 * b ^ 2 + 6 * m ^ 2), Real.sq_sqrt (show 0 ≤ (3 - 2 * b ^ 2 + 6 * m ^ 2 : ℝ) by nlinarith [h1, sq_nonneg m] ), sq_nonneg (m), h1]
    · -- Show that (x, y) ∈ N
      ring_nf