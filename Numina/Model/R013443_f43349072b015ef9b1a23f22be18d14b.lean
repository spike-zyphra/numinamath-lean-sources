import Mathlib

theorem algebra_263073 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2)
    (M : ℝ × ℝ) (hM : M = (1, -1 / 4)) :
    ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ f x1 = -1 / 4 + (2 * Real.sqrt 5) * (x1 - 1) ∧
    f x2 = -1 / 4 + (2 * Real.sqrt 5) * (x2 - 1) := by
  use (2 * Real.sqrt 5 + Real.sqrt (19 - 8 * Real.sqrt 5)) / 2, (2 * Real.sqrt 5 - Real.sqrt (19 - 8 * Real.sqrt 5)) / 2
  constructor
  · -- Show that x1 ≠ x2.
    by_contra h_eq
    have h1 : Real.sqrt (19 - 8 * Real.sqrt 5) = 0 := by
      nlinarith
    have h3 : Real.sqrt (19 - 8 * Real.sqrt 5) > 0 := by
      apply Real.sqrt_pos.2
      nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    nlinarith [h1, h3]
  constructor
  · -- Show that f(x1) equals the required value
    rw [hf]
    have h_eq : ((2 * Real.sqrt 5 + Real.sqrt (19 - 8 * Real.sqrt 5)) / 2 : ℝ) ^ 2 = -1 / 4 + (2 * Real.sqrt 5) * (( (2 * Real.sqrt 5 + Real.sqrt (19 - 8 * Real.sqrt 5)) / 2 : ℝ ) - 1) := by
      nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (19 - 8 * Real.sqrt 5 : ℝ), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (19 - 8 * Real.sqrt 5 : ℝ) by 
          nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        )
      ]
    exact h_eq
  · -- Show that f(x2) equals the required value
    rw [hf]
    have h_eq : ((2 * Real.sqrt 5 - Real.sqrt (19 - 8 * Real.sqrt 5)) / 2 : ℝ) ^ 2 = -1 / 4 + (2 * Real.sqrt 5) * (( (2 * Real.sqrt 5 - Real.sqrt (19 - 8 * Real.sqrt 5) ) / 2 : ℝ ) - 1) := by
      nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (19 - 8 * Real.sqrt 5 : ℝ), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (19 - 8 * Real.sqrt 5 : ℝ) by 
          nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        )
      ]
    exact h_eq