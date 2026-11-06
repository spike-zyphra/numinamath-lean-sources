import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_184949 :
  IsGreatest {t : ℝ | ∃ x y z, t = (sin (2*x) + sin y + sin (3*z))*(cos (2*x) + cos y + cos (3*z))} 4.5 := by
  constructor
  · -- Show 4.5 is indeed in the set by choosing specific x, y, z
    use Real.pi / 8, Real.pi / 4, Real.pi / 12
    have h1 : sin (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by
      have h2 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
      rw [h2]
      rw [sin_pi_div_four]
    have h2 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have h3 : sin (3 * (Real.pi / 12)) = Real.sqrt 2 / 2 := by
      have h4 : 3 * (Real.pi / 12) = Real.pi / 4 := by ring
      rw [h4]
      rw [sin_pi_div_four]
    have h4 : cos (2 * (Real.pi / 8)) = Real.sqrt 2 / 2 := by
      have h2 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
      rw [h2]
      rw [cos_pi_div_four]
    have h5 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h6 : cos (3 * (Real.pi / 12)) = Real.sqrt 2 / 2 := by
      have h4 : 3 * (Real.pi / 12) = Real.pi / 4 := by ring
      rw [h4]
      rw [cos_pi_div_four]
    simp [h1, h2, h3, h4, h5, h6]
    have h7 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [h7]
  · -- Show that 4.5 is greatest in the set
    intro t ht
    rcases ht with ⟨x, y, z, ht⟩
    have h1 : (sin (2 * x) + sin y + sin (3 * z)) ^ 2 + (cos (2 * x) + cos y + cos (3 * z)) ^ 2 ≤ 9 := by
      nlinarith [sq_nonneg (sin (2 * x) - sin y), sq_nonneg (sin y - sin (3 * z)), sq_nonneg (sin (3 * z) - sin (2 * x)),
        sq_nonneg (cos (2 * x) - cos y), sq_nonneg (cos y - cos (3 * z)), sq_nonneg (cos (3 * z) - cos (2 * x)),
        Real.sin_sq_add_cos_sq (2 * x), Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq (3 * z)
        ]
    nlinarith [sq_nonneg (sin (2 * x) + sin y + sin (3 * z) - (cos (2 * x) + cos y + cos (3 * z))), sq_nonneg (sin (2 * x) + sin y + sin (3 * z) + (cos (2 * x) + cos y + cos (3 * z))), Real.sin_sq_add_cos_sq (2 * x), Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq (3 * z)
      ]