import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_291777 :
  IsGreatest {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 3 ∧ t = sqrt x + sqrt (2 * y + 2) + sqrt (3 * z + 6)} 6 := by
  constructor
  · -- Show that 6 is in the set.
    use 1, 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Show that t = sqrt x + sqrt (2 * y + 2) + sqrt (3 * z + 6)
      have h1 : sqrt (1 : ℝ) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : sqrt (2 * (1 : ℝ) + 2) = 2 := by
        rw [show (2 * (1 : ℝ) + 2) = (4 : ℝ) by norm_num]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h3 : sqrt (3 * (1 : ℝ) + 6) = 3 := by
        rw [show (3 * (1 : ℝ) + 6) = (9 : ℝ) by norm_num]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2, h3]
      all_goals norm_num
  · -- Show that 6 is greatest in the set
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, ht⟩
    have h2 : sqrt x + sqrt (2 * y + 2) + sqrt (3 * z + 6) ≤ 6 := by
      nlinarith [sq_nonneg (sqrt x - 1), sq_nonneg (sqrt (2 * y + 2) - 2), sq_nonneg (sqrt (3 * z + 6) - 3),
        Real.sqrt_nonneg x, Real.sqrt_nonneg (2 * y + 2), Real.sqrt_nonneg (3 * z + 6),
        Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * y + 2 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 3 * z + 6 by nlinarith), 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
      ]
    linarith [ht, h2]