import Mathlib

open Real Set
open scoped Real
/-suppose 0 < θ < π, then the maximum value of sinθ/2(1+cosθ) is ?-/
theorem algebra_296295 (θ : ℝ) (hθ : 0 < θ ∧ θ < π) :
    sin (θ / 2) * (1 + cos θ) ≤ 4 * sqrt 3 / 9 := by
  --first expand cosθ --
  have h1 : 1 + cos θ = 2 * cos (θ / 2) ^ 2 := by
    have hcos : cos θ = 2 * cos (θ / 2) ^ 2 - 1 := by
      rw [← cos_two_mul (θ / 2)]
      ring_nf
    linarith
  rw [h1]
  have h2 : sin (θ / 2) * (2 * cos (θ / 2) ^ 2) = 2 * sin (θ / 2) * cos (θ / 2) ^ 2 := by ring
  rw [h2]
  -- it can be proved by AM-GM, or just use nlinarith to make up  squares here --
  have h3 : 2 * sin (θ / 2) * cos (θ / 2) ^ 2 ≤ 4 * sqrt 3 / 9 := by
    nlinarith [sq_nonneg (sin (θ / 2) - sqrt 3 / 3), sq_nonneg (cos (θ / 2)), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sin_sq_add_cos_sq (θ / 2), Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < θ / 2) (by linarith : θ / 2 < Real.pi),
      Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), mul_self_nonneg (Real.sqrt 3 - 3 * sin (θ / 2)), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  linarith