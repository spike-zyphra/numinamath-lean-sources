import Mathlib

open Real Set
open scoped Real

theorem algebra_184790 :
  IsGreatest {x | ∃ (a b c : ℝ), x = (sin a + sin (2*b) + sin (3*c))*(cos a + cos (2*b) + cos (3*c))} 4.5 := by 
  constructor
  · -- Show that 4.5 is in the set 
    use Real.pi / 4, Real.pi / 8, Real.pi / 12
    have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have h2 : sin (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by 
      have h3 : 2 * (Real.pi / 8) = Real.pi / 4 := by
        ring 
      rw [h3] 
      exact h1 
    have h3 : sin (3 * (Real.pi / 12)) = Real.sqrt 2 / 2 := by 
      have h4 : 3 * (Real.pi / 12) = Real.pi / 4 := by 
        ring 
      rw [h4]
      exact h1 
    have hcos1 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by 
      rw [cos_pi_div_four]
    have hcos2 : cos (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by
      have h5 : 2 * (Real.pi / 8) = Real.pi / 4 := by 
        ring 
      rw [h5]
      exact hcos1 
    have hcos3 : cos (3 * (Real.pi / 12)) = Real.sqrt 2 / 2 := by 
      have h6 : 3 * (Real.pi / 12) = Real.pi / 4 := by 
        ring 
      rw [h6]
      exact hcos1
    simp [h1, h2, h3, hcos1, hcos2, hcos3] 
    <;> 
    nlinarith [Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show that 4.5 is the greatest element in the set
    intro x hx 
    rcases hx with ⟨a, b, c, hx⟩
    have h1 : (sin a + sin (2 * b) + sin (3 * c)) * (cos a + cos (2 * b) + cos (3 * c)) ≤ 4.5 := by 
      have h3 : (sin a + sin (2 * b) + sin (3 * c)) ^ 2 + (cos a + cos (2 * b) + cos (3 * c)) ^ 2 ≤ 9 := by 
        nlinarith [sq_nonneg (sin a - sin (2 * b)), sq_nonneg (sin (2 * b) - sin (3 * c)), sq_nonneg (sin a - sin (3 * c)), sq_nonneg (cos a - cos (2 * b)), sq_nonneg (cos (2 * b) - cos (3 * c)), sq_nonneg (cos a - cos (3 * c)), Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq (2 * b), Real.sin_sq_add_cos_sq (3 * c), sq_nonneg (sin a * cos a - sin (2 * b) * cos (2 * b)), sq_nonneg (sin a * cos a - sin (3 * c) * cos (3 * c)), sq_nonneg (sin (2 * b) * cos (2 * b) - sin (3 * c) * cos (3 * c))]
      nlinarith [sq_nonneg ((sin a + sin (2 * b) + sin (3 * c)) - (cos a + cos (2 * b) + cos (3 * c))), sq_nonneg (sin a + sin (2 * b) + sin (3 * c) + (cos a + cos (2 * b) + cos (3 * c))), h3]
    linarith [hx, h1]