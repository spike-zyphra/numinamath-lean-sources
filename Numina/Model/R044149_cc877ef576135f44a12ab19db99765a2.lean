import Mathlib

open Real Set
open scoped Real

theorem algebra_296295 (θ : ℝ) (hθ : 0 < θ ∧ θ < π) :
    sin (θ / 2) * (1 + cos θ) ≤ 4 * sqrt 3 / 9 := by
  have h1 : 1 + cos θ = 2 * cos (θ / 2) ^ 2 := by
    have hcos : cos θ = 2 * cos (θ / 2) ^ 2 - 1 := by
      rw [← cos_two_mul (θ / 2)]
      ring_nf
    linarith [hcos]

  have h3 : sin (θ / 2) > 0 := by
    have hθ1 : 0 < θ / 2 := by linarith [hθ.left, hθ.right]
    have hθ2 : θ / 2 < π / 2 := by
      nlinarith [hθ.left, hθ.right, Real.pi_pos]
    have h1 : sin (θ / 2) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals
        linarith [hθ1, hθ2, Real.pi_pos]
    linarith

  have h4 : cos (θ / 2) > 0 := by
    have hθ1 : 0 < θ / 2 := by linarith [hθ.left, hθ.right]
    have hθ2 : θ / 2 < π / 2 := by
      nlinarith [hθ.left, hθ.right, Real.pi_pos]
    have h1 : cos (θ / 2) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor <;> linarith [hθ1, hθ2, Real.pi_pos]
    linarith

  rw [h1]

  have h11 : sin (θ / 2) * (2 * cos (θ / 2) ^ 2) ≤ 4 * sqrt 3 / 9 := by

    have h12 : cos (θ / 2) ^ 2 = 1 - sin (θ / 2) ^ 2 := by
      have h8 : cos (θ / 2) ^ 2 + sin (θ / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq (θ / 2)
      linarith [h8]

    have h10 : sin (θ / 2) * (2 * cos (θ / 2) ^ 2) = sin (θ / 2) * (2 * (1 - sin (θ / 2) ^ 2)) := by
      have hcos : cos (θ / 2) ^ 2 = 1 - sin (θ / 2) ^ 2 := h12
      simp [hcos]

    have h31 : sin (θ / 2) * (2 * (1 - sin (θ / 2) ^ 2)) ≤ 4 * sqrt 3 / 9 := by

      have h60 : sin (θ / 2) > 0 := h3
      have h61 : sin (θ / 2) < 1 := by
        have h01 : θ / 2 < π / 2 := by
          nlinarith [hθ.left, hθ.right, Real.pi_pos]
        have h612 : sin (θ / 2) < sin (π / 2) := by
          apply sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals
            nlinarith [Real.pi_pos, hθ.left, hθ.right]
        have h88 : sin (π / 2) = 1 := by
          rw [sin_pi_div_two]
        linarith [h88, h612]

      nlinarith [sq_nonneg (sin (θ / 2) ^ 2 - 1 / 3), sq_nonneg (sin (θ / 2) - Real.sqrt 3 / 3), sq_nonneg (sin (θ / 2) + Real.sqrt 3 / 3), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sin_sq_add_cos_sq (θ / 2), Real.sqrt_nonneg 3, sq_nonneg (sin (θ / 2) ^ 2 - 1 / 3)]

    have h33 : sin (θ / 2) * (2 * cos (θ / 2) ^ 2) = sin (θ / 2) * (2 * (1 - sin (θ / 2) ^ 2)) := h10
    rw [h33]
    linarith [h31]

  linarith [h11]