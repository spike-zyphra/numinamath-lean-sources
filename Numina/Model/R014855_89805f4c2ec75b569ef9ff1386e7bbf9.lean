import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_185038 :
  IsGreatest {t : ℝ | ∃ x y z, t = (sin (2 * x) + sin (3 * y) + sin (4 * z)) *
    (cos (2 * x) + cos (3 * y) + cos (4 * z))} 4.5 := by 
  constructor
  · -- Show 4.5 is in the set.
    use Real.pi / 8, Real.pi / 12, Real.pi / 16
    have h1 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
    have h2 : 3 * (Real.pi / 12) = Real.pi / 4 := by ring
    have h3 : 4 * (Real.pi / 16) = Real.pi / 4 := by ring
    rw [h1]
    rw [h2]
    rw [h3]
    have h4 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have h5 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    rw [h4, h5]
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ 2)]
  · -- Show that 4.5 is greatest
    intro t ht
    rcases ht with ⟨x, y, z, ht⟩
    have h : (sin (2 * x) + sin (3 * y) + sin (4 * z)) * (cos (2 * x) + cos (3 * y) + cos (4 * z)) ≤ (4.5 : ℝ) := by
      nlinarith [sq_nonneg (sin (2 * x) - sin (3 * y)), sq_nonneg (sin (2 * x) - sin (4 * z)), sq_nonneg (sin (3 * y) - sin (4 * z)), 
          sq_nonneg (cos (2 * x) - cos (3 * y)), sq_nonneg (cos (2 * x) - cos (4 * z)), sq_nonneg (cos (3 * y) - cos (4 * z)), 
          sq_nonneg (sin (2 * x) + sin (3 * y) + sin (4 * z) - (cos (2 * x) + cos (3 * y) + cos (4 * z))), 
          sq_nonneg ((sin (2 * x) - cos (2 * x))), 
          sq_nonneg ((sin (3 * y) - cos (3 * y))), 
          sq_nonneg ((sin (4 * z) - cos (4 * z))), 
          Real.sin_sq_add_cos_sq (2 * x), 
          Real.sin_sq_add_cos_sq (3 * y), 
          Real.sin_sq_add_cos_sq (4 * z)
        ]
    linarith