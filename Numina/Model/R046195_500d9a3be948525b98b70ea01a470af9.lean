import Mathlib

open Real Set
open scoped Real

theorem inequalities_603349 (α : Real) (hα : α ∈ Icc 0 (π / 2)) :
    2 ≤ sqrt (5 - 4 * sin α) + sin α ∧
    sqrt (5 - 4 * sin α) + sin α ≤ 9 / 4 := by
  rcases hα with ⟨hα1, hα2⟩
  have h1 : 0 ≤ sin α := by
    apply sin_nonneg_of_nonneg_of_le_pi
    linarith [Real.pi_pos, hα1, hα2]
    linarith [Real.pi_pos, hα1, hα2]
  have h2 : sin α ≤ 1 := by
    apply sin_le_one
  have h3 : 0 ≤ 5 - 4 * sin α := by
    nlinarith [Real.sin_sq_add_cos_sq α, sq_nonneg (sin α), sq_nonneg (cos α), h1, h2]
  have h6 : 2 ≤ sqrt (5 - 4 * sin α) + sin α := by
    have h7 : sqrt (5 - 4 * sin α) ≥ 2 - sin α := by
      have h8 : (2 - sin α) ^ 2 ≤ (5 - 4 * sin α : ℝ) := by
        nlinarith [Real.sin_sq_add_cos_sq α, sq_nonneg (sin α - 1), sq_nonneg (cos α)]
      have h9 : 0 ≤ (2 - sin α : ℝ) := by
        nlinarith [h1, h2]
      have h10 : (sqrt (5 - 4 * sin α) : ℝ) ≥ (2 - sin α : ℝ) := by
        have h11 : (sqrt (5 - 4 * sin α)) ^ 2 = (5 - 4 * sin α : ℝ) := Real.sq_sqrt (by nlinarith)
        have h12 : (2 - sin α : ℝ) ^ 2 ≤ (5 - 4 * sin α : ℝ) := h8
        have h13 : sqrt (5 - 4 * sin α : ℝ) ≥ (2 - sin α : ℝ) := by
          nlinarith [Real.sqrt_nonneg (5 - 4 * sin α), sq_nonneg (sqrt (5 - 4 * sin α) - (2 - sin α)), Real.sqrt_nonneg (5 - 4 * sin α), h11, h12, h9]
        linarith [h13]
      linarith
    linarith [h7, h1, h2]
  have h7 : sqrt (5 - 4 * sin α) + sin α ≤ 9 / 4 := by
    have h8 : sqrt (5 - 4 * sin α) ≤ (9 / 4 - sin α : ℝ) := by
      have h9 : (sqrt (5 - 4 * sin α)) ^ 2 ≤ ( (9 / 4 - sin α) : ℝ) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq α, h1, h2, Real.sqrt_nonneg (5 - 4 * sin α), Real.sq_sqrt (show 0 ≤ (5 - 4 * sin α : ℝ) by nlinarith), sq_nonneg (sin α - 1 / 4), sq_nonneg (cos α), sq_nonneg ((sqrt (5 - 4 * sin α) : ℝ) - (9 / 4 - sin α) : ℝ)]
      have h10 : 0 ≤ (9 / 4 - sin α : ℝ) := by
        nlinarith [h1, h2]
      nlinarith [Real.sqrt_nonneg (5 - 4 * sin α), Real.sq_sqrt (show 0 ≤ (5 - 4 * sin α : ℝ) by nlinarith), h9, h10]
    linarith [h8, h1, h2]
  constructor
  · -- Prove 2 ≤ sqrt (5 - 4 * sin α) + sin α
    linarith [h6]
  · -- Prove sqrt (5 - 4 * sin α) + sin α ≤ 9 / 4
    linarith [h7]