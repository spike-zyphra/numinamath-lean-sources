import Mathlib

open Real Set
open scoped Real

theorem algebra_277616 (θ : ℝ) (hθ : 0 < θ ∧ θ < π) :
    sin (θ / 2) * (1 + cos θ) ≤ 4 * sqrt 3 / 9 := by
  have h1 : 0 < θ := hθ.1
  have h2 : θ < π := hθ.2
  have h3 : 0 < θ / 2 := by linarith
  have h4 : θ / 2 < π / 2 := by
    have h5 : θ < π := h2
    nlinarith
  have h5 : sin (θ / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h6 : cos (θ / 2) > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith
  have h7 : 1 + cos θ = 2 * cos (θ / 2) ^ 2 := by
    have hcos : cos θ = 2 * cos (θ / 2) ^ 2 - 1 := by
      rw [← Real.cos_two_mul (θ / 2)]
      all_goals ring_nf
      <;> simp [Real.cos_sq]
      all_goals ring
    linarith
  have h8 : sin (θ / 2) * (1 + cos θ) = 2 * sin (θ / 2) * cos (θ / 2) ^ 2 := by
    rw [h7]
    all_goals ring
  rw [h8]
  have h9 : sin (θ / 2) ^ 2 + cos (θ / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (θ / 2)
  nlinarith [sq_nonneg (2 * sin (θ / 2) - sqrt 3 / 3 * 4),
    sq_nonneg (cos (θ / 2) ^ 2 - 1 / 3),
    sq_nonneg (sin (θ / 2) - sqrt 3 / 3),
    sq_nonneg (sin (θ / 2) * cos (θ / 2) - sqrt 3 / 3 / 2),
    Real.sqrt_nonneg 3,
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
    Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (3 : ℝ) > 0),
    h9,
    sq_nonneg (sin (θ / 2) - cos (θ / 2) * (sqrt 3 / 3) * 2),
    sq_nonneg (2 * sin (θ / 2) * cos (θ / 2) - sqrt 3 / 3 * 2)
  ]