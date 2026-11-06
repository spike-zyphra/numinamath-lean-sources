import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_185664 :
  IsGreatest {x | ∃ (a b c : ℝ), x = (sin (3*a) + sin (2*b) + sin c)*(cos (3*a) + cos (2*b) + cos c)} 4.5 := by 
  constructor 
  · -- Show 4.5 is in the set
    use Real.pi / 12, Real.pi / 8, Real.pi / 4
    have h1 : sin (3 * (Real.pi / 12)) = Real.sqrt 2 / 2 := by
      have h2 : 3 * (Real.pi / 12) = Real.pi / 4 := by ring 
      rw [h2]
      have h3 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := sin_pi_div_four 
      exact h3 
    have h2 : sin (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by
      have h3 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring 
      rw [h3]
      have h4 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := sin_pi_div_four 
      exact h4 
    have h3 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := sin_pi_div_four
    have h4 : cos (3 * (Real.pi / 12)) = Real.sqrt 2 / 2 := by
      have h5 : 3 * (Real.pi / 12) = Real.pi / 4 := by ring 
      rw [h5]
      have h6 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := cos_pi_div_four
      exact h6 
    have h5 : cos (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by
      have h6 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring 
      rw [h6]
      have h7 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := cos_pi_div_four
      exact h7 
    have h6 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := cos_pi_div_four 
    rw [h1, h2, h3, h4, h5, h6]
    field_simp
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show 4.5 is greatest
    intro x hx 
    rcases hx with ⟨a, b, c, hx⟩ 
    have h1 : (sin (3 * a) + sin (2 * b) + sin c) ^ 2 + (cos (3 * a) + cos (2 * b) + cos c) ^ 2 ≤ 9 := by 
      nlinarith [sq_nonneg (sin (3 * a) - sin (2 * b)), sq_nonneg (sin (3 * a) - sin c), sq_nonneg (sin (2 * b) - sin c),
                  sq_nonneg (cos (3 * a) - cos (2 * b)), sq_nonneg (cos (3 * a) - cos c), sq_nonneg (cos (2 * b) - cos c),
                  Real.sin_sq_add_cos_sq (3 * a), Real.sin_sq_add_cos_sq (2 * b), Real.sin_sq_add_cos_sq c
                 ]
    nlinarith [sq_nonneg ((sin (3 * a) + sin (2 * b) + sin c) - (cos (3 * a) + cos (2 * b) + cos c)), 
              Real.sin_sq_add_cos_sq (3 * a), Real.sin_sq_add_cos_sq (2 * b), Real.sin_sq_add_cos_sq c
             ]