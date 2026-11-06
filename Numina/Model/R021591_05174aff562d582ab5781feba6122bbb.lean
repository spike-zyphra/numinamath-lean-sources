import Mathlib

open Real Set
open scoped Real

theorem algebra_184867 :
  IsGreatest {x | ∃ a b c : ℝ, x = (sin (3*a) + sin (2*b) + sin c) *
    (cos (3*a) + cos (2*b) + cos c)} 4.5 := by
  constructor
  · -- Show that 4.5 is achievable by choosing specific angles
    use Real.pi / 12, Real.pi / 8, Real.pi / 4
    have h1 : sin (3 * (Real.pi / 12)) = Real.sqrt 2 / 2 := by
      have h2 : 3 * (Real.pi / 12) = Real.pi / 4 := by
        ring
      rw [h2]
      have h3 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        exact sin_pi_div_four
      rw [h3]
    have h2 : sin (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by
      have h4 : 2 * (Real.pi / 8) = Real.pi / 4 := by
        ring
      rw [h4]
      have h5 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        exact sin_pi_div_four
      rw [h5]
    have h3 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      exact sin_pi_div_four
    have h4 : cos (3 * (Real.pi / 12)) = Real.sqrt 2 / 2 := by
      have h5 : 3 * (Real.pi / 12) = Real.pi / 4 := by
        ring
      rw [h5]
      have h6 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        exact cos_pi_div_four
      rw [h6]
    have h5 : cos (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by
      have h6 : 2 * (Real.pi / 8) = Real.pi / 4 := by
        ring
      rw [h6]
      have h7 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        exact cos_pi_div_four
      rw [h7]
    have h6 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      exact cos_pi_div_four
    rw [h1, h2, h3, h4, h5, h6]
    have h7 : (Real.sqrt 2 / 2 + Real.sqrt 2 / 2 + Real.sqrt 2 / 2) * (Real.sqrt 2 / 2 + Real.sqrt 2 / 2 + Real.sqrt 2 / 2) = 4.5 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    linarith [h7]
  · -- Show that 4.5 is indeed the greatest value
    intro x hx
    rcases hx with ⟨a, b, c, hx⟩
    have h1 : (sin (3 * a) + sin (2 * b) + sin c) ^ 2 + (cos (3 * a) + cos (2 * b) + cos c) ^ 2 ≤ 9 := by
      nlinarith [sq_nonneg (sin (3 * a) - sin (2 * b)), sq_nonneg (sin (3 * a) - sin c), sq_nonneg (sin (2 * b) - sin c),
                sq_nonneg (cos (3 * a) - cos (2 * b)), sq_nonneg (cos (3 * a) - cos c), sq_nonneg (cos (2 * b) - cos c),
                Real.sin_sq_add_cos_sq (3 * a), Real.sin_sq_add_cos_sq (2 * b), Real.sin_sq_add_cos_sq c, 
                sq_nonneg (sin (3 * a) + sin (2 * b) + sin c), sq_nonneg (cos (3 * a) + cos (2 * b) + cos c), 
                sq_nonneg (sin (3 * a) - cos (3 * a)), sq_nonneg (sin (2 * b) - cos (2 * b)), sq_nonneg (sin c - cos c)]
    have h2 : (sin (3 * a) + sin (2 * b) + sin c) * (cos (3 * a) + cos (2 * b) + cos c) ≤ 4.5 := by
      nlinarith [sq_nonneg ((sin (3 * a) + sin (2 * b) + sin c) - (cos (3 * a) + cos (2 * b) + cos c)), 
                sq_nonneg ((sin (3 * a) + sin (2 * b) + sin c) + (cos (3 * a) + cos (2 * b) + cos c)), 
                h1, Real.sin_sq_add_cos_sq (3 * a), Real.sin_sq_add_cos_sq (2 * b), Real.sin_sq_add_cos_sq c]
    linarith [h2, hx]