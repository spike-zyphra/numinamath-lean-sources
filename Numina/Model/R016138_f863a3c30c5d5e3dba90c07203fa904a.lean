import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem inequalities_149175 (x : ℝ) (hx : 0 < x ∧ x < π) :
    sin x + (1/2)*sin (2*x) + (1/3)*sin (3*x) > 0 :=
  by
    have hx1 : 0 < x := hx.1
    have hx2 : x < π := hx.2
    have h1 : sin x > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith
      linarith
    have h2 : sin (2 * x) = 2 * sin x * cos x := by 
      rw [sin_two_mul]
    have h3 : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
      rw [sin_three_mul]
    rw [h2, h3]
    have eq : sin x + (1 / 2) * (2 * sin x * cos x) + (1 / 3) * (3 * sin x - 4 * sin x ^ 3) = 
      sin x * (2 + cos x - (4 / 3) * sin x ^ 2) := by
      ring
    rw [eq]
    have h4 : 2 + cos x - (4 / 3) * sin x ^ 2 > 0 := by
      have h5 : sin x ^ 2 = 1 - cos x ^ 2 := by 
        rw [←Real.cos_sq_add_sin_sq x]
        linarith
      rw [h5]
      nlinarith [Real.cos_sq_add_sin_sq x, sq_nonneg (cos x), sq_nonneg (cos x - -1/8), sq_nonneg ((-1/8 : ℝ) * (cos x) - -1/40), sq_nonneg (cos x - -1/2), sq_nonneg (cos x + 1/2), sq_nonneg (cos x - 1/2), sq_nonneg (cos x + 1/8)]
    apply mul_pos
    · linarith
    · nlinarith