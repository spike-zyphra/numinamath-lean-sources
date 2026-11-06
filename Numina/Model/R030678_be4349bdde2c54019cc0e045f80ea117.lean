import Mathlib

open Real

theorem calculus_1765 (f : ℝ → ℝ) (hf : f = fun x => (x^2 - 6 * x - 5) / (x - 2)) :
    ∀ y, ∃ x, 2 < x ∧ f x = y := by
  intro y
  have h1 : 0 < (y ^ 2 + 4 * y + 56 : ℝ) := by
    nlinarith [sq_nonneg (y + 2)]
  have h2 : 0 < Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) := by
    positivity
  have h3 : 0 < Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) + (y + 2) := by
    by_cases h4 : (y + 2 : ℝ) ≥ 0
    · -- Case 1: $y + 2 \geq 0$
      nlinarith [Real.sqrt_nonneg (y ^ 2 + 4 * y + 56 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 4 * y + 56 by nlinarith)]
    · -- Case 2: $y + 2 < 0$
      have h5 : (y + 2 : ℝ) < (0 : ℝ) := by linarith
      have h7 : Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) > (- (y + 2 : ℝ)) := by
        have h8 : Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) ^ 2 > (- (y + 2 : ℝ)) ^ 2 := by
          have h9 : Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) ^ 2 = y ^ 2 + 4 * y + 56 := by
            rw [Real.sq_sqrt]
            nlinarith
          have h10 : (- (y + 2 : ℝ)) ^ 2 = (y + 2 : ℝ) ^ 2 := by ring
          nlinarith [h10, h9]
        nlinarith [Real.sqrt_nonneg (y ^ 2 + 4 * y + 56 : ℝ)]
      nlinarith [Real.sqrt_nonneg (y ^ 2 + 4 * y + 56 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 4 * y + 56 by nlinarith)]
  use (y + 6 + Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ)) / 2
  constructor
  · -- Show that 2 < x
    nlinarith [Real.sqrt_nonneg (y ^ 2 + 4 * y + 56 : ℝ), h3]
  · -- Show that f x = y
    rw [hf]
    have hx1 : ( (y + 6 + Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) ) / 2 ) - 2 ≠ 0 := by
      have h16 : ( (y + 6 + Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) ) / 2 ) - 2 = ( Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) + (y + 2) ) / 2 := by 
        ring_nf
      rw [h16]
      apply div_ne_zero 
      · -- Show sqrt ... + ... ≠ 0
        nlinarith [Real.sqrt_nonneg (y ^ 2 + 4 * y + 56 : ℝ), h3]
      · -- Show 2 ≠ 0 
        norm_num

    have h_eq1 : ( ( (y + 6 + Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) ) / 2 ) ^ 2 - 6 * ( (y + 6 + Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) ) / 2 ) - 5 ) = y * ( ( (y + 6 + Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) ) / 2 ) - 2 ) := by
      nlinarith [Real.sqrt_nonneg (y ^ 2 + 4 * y + 56 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 4 * y + 56 by nlinarith) ]

    have h_eq2 : ( ( (y + 6 + Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) ) / 2 ) ^ 2 - 6 * ( (y + 6 + Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) ) / 2 ) - 5 ) / ( ( (y + 6 + Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) ) / 2 ) - 2 ) = y := by 
      rw [div_eq_iff (show ( (y + 6 + Real.sqrt (y ^ 2 + 4 * y + 56 : ℝ) ) / 2 ) - 2 ≠ 0 by exact hx1 ) ]
      linarith [h_eq1]
    simpa using h_eq2