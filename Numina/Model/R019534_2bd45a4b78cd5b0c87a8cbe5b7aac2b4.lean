import Mathlib

open Real Set

theorem algebra_102686 :
    IsLeast {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ (x + y + z) * x * y * z = 4 ∧ t = (x + y) ^ 2 + (y + z) ^ 2 + (z + x) ^ 2} (8 * sqrt 3) := by
  constructor
  · -- Show that 8 * sqrt 3 is in the set
    use (Real.sqrt (2 * Real.sqrt 3 / 3)), (Real.sqrt (2 * Real.sqrt 3 / 3)), (Real.sqrt (2 * Real.sqrt 3 / 3))
    constructor
    · -- Show x > 0
      positivity
    constructor
    · -- Show y > 0
      positivity
    constructor
    · -- Show z > 0
      positivity
    constructor
    · -- Show (x + y + z) * x * y * z = 4
      have h1 : Real.sqrt (2 * Real.sqrt 3 / 3) ^ 2 = 2 * Real.sqrt 3 / 3 := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 * Real.sqrt 3 / 3) by positivity), 
        mul_pos (show (0 : ℝ) < Real.sqrt 3 by positivity) (show (0 : ℝ) < 2 by norm_num), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 * Real.sqrt 3 / 3) by positivity), 
        sq_nonneg (Real.sqrt 3 ^ 2 - 3), Real.sqrt_nonneg 3
      ]
    · -- Show 8 * sqrt 3 = (x + y) ^ 2 + (y + z) ^ 2 + (z + x) ^ 2
      have h1 : Real.sqrt (2 * Real.sqrt 3 / 3) ^ 2 = 2 * Real.sqrt 3 / 3 := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 * Real.sqrt 3 / 3) by positivity), 
        mul_pos (show (0 : ℝ) < Real.sqrt 3 by positivity) (show (0 : ℝ) < 2 by norm_num), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 * Real.sqrt 3 / 3) by positivity), 
        sq_nonneg (Real.sqrt 3 ^ 2 - 3), Real.sqrt_nonneg 3
      ]
  · -- Show that 8 * sqrt 3 is minimality
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, ht⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
      sq_nonneg ((x + y + z) ^ 2 - 4 * Real.sqrt 3), 
      sq_nonneg (x * y * z - Real.sqrt 3), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), 
      mul_pos (show (0 : ℝ) < x * y * z by positivity) (show (0 : ℝ) < x + y + z by positivity), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
      sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
    ]