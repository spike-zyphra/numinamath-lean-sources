import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_121890 :
  IsLeast {y : ℝ | ∃ x, y = sin (π * x) / sqrt (1 + x + x ^ 2)} (-2 * sqrt 3 / 3) := by
  constructor
  · -- Show that -2 * sqrt 3 / 3 is attained at x = -1/2
    use -1 / 2
    have h1 : sin (π * (-1 / 2)) = -1 := by
      have h2 : π * (-1 / 2) = -(π / 2) := by ring
      rw [h2]
      rw [sin_neg]
      norm_num
    have h2 : (1 + (-1 / 2 : ℝ) + (-1 / 2 : ℝ) ^ 2 : ℝ) = (3 / 4 : ℝ) := by norm_num
    have h3 : sqrt (1 + (-1 / 2 : ℝ) + (-1 / 2 : ℝ) ^ 2) = Real.sqrt 3 / 2 := by
      rw [h2]
      have h4 : Real.sqrt ((3 / 4 : ℝ)) = Real.sqrt (3) / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      rw [h4]
    rw [h1, h3]
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.pi_pos]
  · -- Show that -2 * sqrt 3 / 3 is a lower bound
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : -1 ≤ sin (π * x) := by
      linarith [neg_one_le_sin (π * x), sin_le_one (π * x)]
    have h2 : (1 + x + x ^ 2) ≥ (3 / 4 : ℝ) := by
      nlinarith [sq_nonneg (x + 1 / 2)]
    have h3 : sqrt (1 + x + x ^ 2) ≥ Real.sqrt 3 / 2 := by
      have h4 : (1 + x + x ^ 2 : ℝ) ≥ (3 / 4 : ℝ) := h2
      have h5 : sqrt (1 + x + x ^ 2) ≥ sqrt (3 / 4 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h6 : sqrt (3 / 4 : ℝ) = Real.sqrt 3 / 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      linarith [h5, h6]
    have h4 : sin (π * x) ≥ -1 := by
      linarith [neg_one_le_sin (π * x), sin_le_one (π * x)]
    have h6 : sin (π * x) ≥ (-2 * Real.sqrt 3 / 3) * sqrt (1 + x + x ^ 2) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg (1 + x + x ^ 2), h1, h4, h3, 
        Real.sq_sqrt (show (0 : ℝ) ≤ 1 + x + x ^ 2 by nlinarith), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), 
        Real.sin_sq_add_cos_sq (π * x), Real.sin_sq_le_one (π * x)]
    have h7 : sin (π * x) / sqrt (1 + x + x ^ 2) ≥ -2 * Real.sqrt 3 / 3 := by
      have h8 : sqrt (1 + x + x ^ 2) > 0 := by
        apply Real.sqrt_pos.mpr
        nlinarith [sq_nonneg x]
      apply (le_div_iff₀ h8).mpr
      linarith [h6, Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)]
    linarith [h7, hx]