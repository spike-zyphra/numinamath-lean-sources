import Mathlib

open Real Set
open scoped Real

theorem algebra_185798 :
  IsGreatest {x | ∃ a b c : ℝ, x = (sin (2*a) + sin (3*b) + sin (4*c))*(cos (2*a) + cos (3*b) + cos (4*c))} 4.5 := by
  constructor
  · -- Show 4.5 in the set
    use Real.pi / 8, Real.pi / 12, Real.pi / 16
    have h1 : sin (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by
      have h1 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
      rw [h1]
      rw [sin_pi_div_four]
    have h2 : sin (3 * (Real.pi / 12)) = Real.sqrt 2 / 2 := by
      have h2 : 3 * (Real.pi / 12) = Real.pi / 4 := by ring
      rw [h2]
      rw [sin_pi_div_four]
    have h3 : sin (4 * (Real.pi / 16)) = Real.sqrt 2 / 2 := by 
      have h3 : 4 * (Real.pi / 16) = Real.pi / 4 := by ring
      rw [h3]
      rw [sin_pi_div_four]
    have h4 : cos (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by 
      have h4 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
      rw [h4]
      rw [cos_pi_div_four]
    have h5 : cos (3 * (Real.pi / 12)) = Real.sqrt 2 / 2 := by 
      have h5 : 3 * (Real.pi / 12) = Real.pi / 4 := by ring
      rw [h5]
      rw [cos_pi_div_four]
    have h6 : cos (4 * (Real.pi / 16)) = Real.sqrt 2 / 2 := by 
      have h6 : 4 * (Real.pi / 16) = Real.pi / 4 := by ring
      rw [h6]
      rw [cos_pi_div_four]
    rw [h1, h2, h3, h4, h5, h6]
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  · -- Show 4.5 is greatest element in the set
    intro x hx
    rcases hx with ⟨a, b, c, hx⟩
    nlinarith [sq_nonneg ((sin (2 * a) + sin (3 * b) + sin (4 * c)) - (cos (2 * a) + cos (3 * b) + cos (4 * c))), 
                sq_nonneg (sin (2 * a) - cos (2 * a)), 
                sq_nonneg (sin (3 * b) - cos (3 * b)), 
                sq_nonneg (sin (4 * c) - cos (4 * c)), 
                Real.sin_sq_add_cos_sq (2 * a), 
                Real.sin_sq_add_cos_sq (3 * b), 
                Real.sin_sq_add_cos_sq (4 * c),
                sq_nonneg (sin (2 * a) - sin (3 * b)), 
                sq_nonneg (sin (3 * b) - sin (4 * c)), 
                sq_nonneg (sin (4 * c) - sin (2 * a)), 
                sq_nonneg (cos (2 * a) - cos (3 * b)), 
                sq_nonneg (cos (3 * b) - cos (4 * c)), 
                sq_nonneg (cos (4 * c) - cos (2 * a))
            ]