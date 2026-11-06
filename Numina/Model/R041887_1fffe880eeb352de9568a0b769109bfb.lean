import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_137019 :
  IsLeast {A : ℝ | ∀ x y z w, x * y + 2 * y * z + z * w ≤ A * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2)} ((1 + √2) / 2) := by
  constructor
  · -- Show that (1 + √2) / 2 is in the set.
    intro x y z w 
    have h2 : x * y + 2 * y * z + z * w ≤ ((1 + √2) / 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
      nlinarith [sq_nonneg (x - w), sq_nonneg (y - z), sq_nonneg (x + w - (y + z)), 
        sq_nonneg (x + w + y + z), sq_nonneg (x - w - (y - z)), sq_nonneg (x - w + (y - z)), 
        sq_nonneg (y - (1 + Real.sqrt 2) * x), sq_nonneg (z - (1 + Real.sqrt 2) * w), 
        sq_nonneg (x - w), sq_nonneg (y - z), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        sq_nonneg (y + z - (x + w)), 
        sq_nonneg ((x + w) - (y + z) * Real.sqrt 2 / 2), 
        sq_nonneg ((y - z) * Real.sqrt 2 - (x - w)), 
        sq_nonneg (x + w - y - z), sq_nonneg (x - w + y - z), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      ]
    linarith
  · -- Show that (1 + √2) / 2 is minimal
    intro A h 
    have h1 : ∀ x y z w, x * y + 2 * y * z + z * w ≤ A * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := h 
    have h22 := h1 1 (1 + Real.sqrt 2) (1 + Real.sqrt 2) 1 
    have h3 : (1 + Real.sqrt 2) / 2 ≤ A := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ)]
    linarith