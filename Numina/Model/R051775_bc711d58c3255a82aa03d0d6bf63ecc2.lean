import Mathlib

theorem algebra_11184 {x : ℝ} (hx : x = (1 + Real.sqrt 3) / (1 - Real.sqrt 3)) :
    ∃ a b c : ℤ, x = a + b * Real.sqrt c ∧ a * b * c = 6 := by
  have hx2 : x = -2 - Real.sqrt 3 := by
    rw [hx]
    -- Multiply numerator and denominator by the conjugate of the denominator
    have h1 : (1 + Real.sqrt 3) / (1 - Real.sqrt 3) = ((1 + Real.sqrt 3) * (1 + Real.sqrt 3)) / ((1 - Real.sqrt 3) * (1 + Real.sqrt 3)) := by
      field_simp [(show (1 - Real.sqrt 3) ≠ 0 by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      )]
      <;> ring
    rw [h1]
    have h2 : (1 - Real.sqrt 3) * (1 + Real.sqrt 3) = -2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h3 : (1 + Real.sqrt 3) * (1 + Real.sqrt 3) = 4 + 2 * Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
        mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
    rw [h2, h3]
    field_simp
    ring
  use -2, -1, 3
  constructor
  · -- Show x = a + b * sqrt c
    rw [hx2]
    ring_nf
  · -- Show a * b * c = 6
    norm_num