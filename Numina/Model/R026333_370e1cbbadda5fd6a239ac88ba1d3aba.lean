import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12168 (f : ℝ → ℝ) (hf : f = λ x => -4 * x + 3 * sqrt (4 * x ^ 2 + 1)) :
    IsLeast (range f) (sqrt 5) := by 
  constructor 
  · -- Show that sqrt 5 is in the range of f
    use Real.sqrt 5 / 5
    rw [hf]
    have h1 : Real.sqrt (4 * (Real.sqrt 5 / 5) ^ 2 + 1) = 3 * Real.sqrt 5 / 5 := by 
      have h2 : (4 * (Real.sqrt 5 / 5) ^ 2 + 1 : ℝ) = (9 / 5 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      rw [h2]
      have h3 : Real.sqrt (9 / 5 : ℝ) = 3 * Real.sqrt 5 / 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      exact h3
    simp [h1]
    field_simp
    nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  · -- Show that sqrt 5 is the least in the range
    intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx 
    have h1 : -4 * x + 3 * Real.sqrt (4 * x ^ 2 + 1) ≥ Real.sqrt 5 := by
      nlinarith [sq_nonneg (x * 5 - Real.sqrt 5 * 2), sq_nonneg (Real.sqrt (4 * x ^ 2 + 1) - 3 * Real.sqrt 5 / 5), 
              sq_nonneg ((-4 * x + 3 * Real.sqrt (4 * x ^ 2 + 1)) - Real.sqrt 5), 
              Real.sqrt_nonneg (4 * x ^ 2 + 1), Real.sqrt_nonneg 5, 
              Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (4 * x ^ 2 + 1 : ℝ) by nlinarith [sq_nonneg x]), 
              mul_nonneg (Real.sqrt_nonneg (5)) (Real.sqrt_nonneg (4 * x ^ 2 + 1)), 
              sq_nonneg (x - Real.sqrt 5 / 5) 
            ]
    have h2 : (-4 * x + 3 * Real.sqrt (4 * x ^ 2 + 1) ) = y := by
      simpa using hx 
    have h3 : Real.sqrt 5 ≤ y := by
      nlinarith [h1, h2]
    linarith