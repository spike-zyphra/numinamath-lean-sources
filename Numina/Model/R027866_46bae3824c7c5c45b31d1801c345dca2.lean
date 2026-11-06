import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_185722 :
  IsGreatest {x | ∃ a b c : ℝ, x = (sin (2*a) + sin b + sin (3*c))*(cos (2*a) + cos b + cos (3*c))} 4.5 := by
  constructor
  · -- Show that 4.5 is in the set.
    use Real.pi / 8, Real.pi / 4, Real.pi / 12
    have h1 : sin (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by 
      have h2 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
      rw [h2] 
      rw [Real.sin_pi_div_four]
    have h2 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by 
      rw [Real.sin_pi_div_four]
    have h3 : sin (3 * (Real.pi / 12)) = Real.sqrt 2 / 2 := by 
      have h4 : 3 * (Real.pi / 12) = Real.pi / 4 := by ring
      rw [h4]
      rw [Real.sin_pi_div_four]
    have h4 : cos (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by 
      have h5 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
      rw [h5]
      rw [Real.cos_pi_div_four]
    have h5 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by 
      rw [Real.cos_pi_div_four]
    have h6 : cos (3 * (Real.pi / 12)) = Real.sqrt 2 / 2 := by 
      have h7 : 3 * (Real.pi / 12) = Real.pi / 4 := by ring
      rw [h7]
      rw [Real.cos_pi_div_four]
    have hx5 : (sin (2 * (Real.pi / 8)) + sin (Real.pi / 4) + sin (3 * (Real.pi / 12))) * (cos (2 * (Real.pi / 8)) + cos (Real.pi / 4) + cos (3 * (Real.pi / 12)) ) = 4.5 := by 
      have hx10 : sin (2 * (Real.pi / 8)) + sin (Real.pi / 4) + sin (3 * (Real.pi / 12)) = 3 * (Real.sqrt 2 / 2) := by 
        linarith [h1, h2, h3]
      have hx20 : cos (2 * (Real.pi / 8)) + cos (Real.pi / 4) + cos (3 * (Real.pi / 12)) = 3 * (Real.sqrt 2 / 2) := by 
        linarith [h4, h5, h6]
      rw [hx10, hx20]
      have h17 : Real.sqrt 2 ^ 2 = 2 := by 
        exact Real.sq_sqrt (by linarith)
      nlinarith [h17, Real.sqrt_nonneg (2)]
    linarith
  · -- Show that 4.5 is the greatest element in the set.
    intro x hx
    rcases hx with ⟨a, b, c, heq⟩
    have h1 : sin (2*a) ^ 2 + cos (2*a) ^ 2 = 1 := by
      have h1 := Real.sin_sq_add_cos_sq (2*a)
      linarith
    have h2 : sin b ^ 2 + cos b ^ 2 = 1 := by
      have h2 := Real.sin_sq_add_cos_sq b
      linarith
    have h3 : sin (3*c) ^ 2 + cos (3*c) ^ 2 = 1 := by
      have h3 := Real.sin_sq_add_cos_sq (3*c)
      linarith
    nlinarith [Real.sin_sq_add_cos_sq (2*a), Real.sin_sq_add_cos_sq b, Real.sin_sq_add_cos_sq (3*c), 
      Real.sin_le_one (2*a), Real.sin_le_one b, Real.sin_le_one (3*c), 
      Real.cos_le_one (2*a), Real.cos_le_one b, Real.cos_le_one (3*c), 
      sq_nonneg (sin (2*a) + sin b + sin (3*c) - (cos (2*a) + cos b + cos (3*c))), 
      sq_nonneg (sin (2*a) - sin b), sq_nonneg (sin b - sin (3*c)), sq_nonneg (sin (3*c) - sin (2*a)), 
      sq_nonneg (cos (2*a) - cos b), sq_nonneg (cos b - cos (3*c)), sq_nonneg (cos (3*c) - cos (2*a)), 
      sq_nonneg (sin (2*a) * cos (2*a)), sq_nonneg (sin b * cos b), sq_nonneg (sin (3*c) * cos (3*c)), 
      mul_self_nonneg (sin (2*a) - cos (2*a)), mul_self_nonneg (sin b - cos b), mul_self_nonneg (sin (3*c) - cos (3*c)), 
      Real.sin_sq_add_cos_sq (2*a), Real.sin_sq_add_cos_sq b, Real.sin_sq_add_cos_sq (3*c)
    ]