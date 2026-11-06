import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_177642 {f : ℝ → ℝ}
  (hf : f = λ x => (sqrt (x - 4 * sqrt (x - 4)) + 2) / (sqrt (x + 4 * sqrt (x - 4)) - 2)) :
  ∀ x, x ∈ Ioo 4 8 → f x = 4 / sqrt (x - 4) - 1 ∧
  ∀ x, x ≥ 8 → f x = 1 := by
  intro x hx
  constructor
  · -- Assume x ∈ (4, 8)
    rcases hx with ⟨hx1, hx2⟩
    rw [hf]
    have h1 : sqrt (x - 4 * sqrt (x - 4)) = 2 - sqrt (x - 4) := by
      have h2 : x - 4 * sqrt (x - 4) = (2 - sqrt (x - 4)) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show 0 ≤ (x - 4 : ℝ) by nlinarith)]
      have h3 : sqrt (x - 4 * sqrt (x - 4)) = sqrt ((2 - sqrt (x - 4)) ^ 2) := by
        rw [h2]
      have h4 : sqrt ((2 - sqrt (x - 4)) ^ 2) = 2 - sqrt (x - 4) := by
        rw [Real.sqrt_sq (show 0 ≤ (2 - sqrt (x - 4) : ℝ) by
          nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show 0 ≤ x - 4 by nlinarith)]
        )]
      rw [h3, h4]
    have h2 : sqrt (x + 4 * sqrt (x - 4)) = sqrt (x - 4) + 2 := by
      have h5 : x + 4 * sqrt (x - 4) = (sqrt (x - 4) + 2) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show 0 ≤ x - 4 by nlinarith)]
      have h6 : sqrt (x + 4 * sqrt (x - 4)) = sqrt ((sqrt (x - 4) + 2) ^ 2) := by
        rw [h5]
      have h7 : sqrt ((sqrt (x - 4) + 2) ^ 2) = sqrt (x - 4) + 2 := by
        rw [Real.sqrt_sq (show 0 ≤ sqrt (x - 4) + 2 by
          nlinarith [Real.sqrt_nonneg (x - 4)]
        )]
      rw [h6, h7]
    simp only [h1, h2]
    have h3 : sqrt (x - 4) > 0 := by
      apply Real.sqrt_pos.mpr
      nlinarith
    field_simp [h3]
    <;> nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show 0 ≤ x - 4 by nlinarith)]
  · -- Assume x ≥ 8
    intro x hx
    rw [hf]
    have h1 : sqrt (x - 4 * sqrt (x - 4)) = sqrt (x - 4) - 2 := by
      have h2 : x - 4 * sqrt (x - 4) = (sqrt (x - 4) - 2) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show 0 ≤ x - 4 by nlinarith)]
      have h3 : sqrt (x - 4 * sqrt (x - 4)) = sqrt ((sqrt (x - 4) - 2) ^ 2) := by
        rw [h2]
      have h4 : sqrt ((sqrt (x - 4) - 2) ^ 2) = sqrt (x - 4) - 2 := by
        rw [Real.sqrt_sq (show 0 ≤ sqrt (x - 4) - 2 by
          have h5 : sqrt (x - 4) ≥ 2 := by
            have h6 : x - 4 ≥ 4 := by linarith
            have h7 : sqrt (x - 4) ≥ sqrt (4 : ℝ) := by
              apply Real.sqrt_le_sqrt
              linarith
            have h8 : sqrt (4 : ℝ) = 2 := Real.sqrt_eq_cases.2 (by norm_num)
            nlinarith [h7, h8]
          linarith
        )]
      rw [h3, h4]
    have h2 : sqrt (x + 4 * sqrt (x - 4)) = sqrt (x - 4) + 2 := by
      have h5 : x + 4 * sqrt (x - 4) = (sqrt (x - 4) + 2) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show 0 ≤ x - 4 by nlinarith)]
      have h6 : sqrt (x + 4 * sqrt (x - 4)) = sqrt ((sqrt (x - 4) + 2) ^ 2) := by
        rw [h5]
      have h7 : sqrt ((sqrt (x - 4) + 2) ^ 2) = sqrt (x - 4) + 2 := by
        rw [Real.sqrt_sq (show 0 ≤ sqrt (x - 4) + 2 by
          nlinarith [Real.sqrt_nonneg (x - 4)]
        )]
      rw [h6, h7]
    simp only [h1, h2]
    have h3 : sqrt (x - 4) > 0 := by
      apply Real.sqrt_pos.mpr
      nlinarith
    field_simp [h3]
    <;> nlinarith [Real.sqrt_nonneg (x - 4), Real.sq_sqrt (show 0 ≤ x - 4 by nlinarith)]