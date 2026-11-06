import Mathlib

open Real Set
open scoped Real

theorem algebra_272171 (θ : ℝ) (hθ : θ ∈ Ioo 0 π) :
    sin (θ / 2) * (1 + cos θ) ≤ 4 * √3 / 9 := by 
  rcases hθ with ⟨h1, h2⟩
  have h3 : 0 < θ / 2 := by linarith
  have h4 : θ / 2 < Real.pi / 2 := by
    nlinarith [Real.pi_gt_three, h2]
  
  have h5 : cos θ = 1 - 2 * sin (θ / 2) ^ 2 := by
    have h6 : cos θ = cos (2 * (θ / 2)) := by ring_nf
    rw [h6]
    rw [cos_two_mul]
    rw [sin_sq]
    <;> ring_nf
  have h7 : 1 + cos θ = 2 * (1 - sin (θ / 2) ^ 2) := by
    rw [h5]
    all_goals ring_nf
  have h8 : sin (θ / 2) * (1 + cos θ) = 2 * sin (θ / 2) - 2 * (sin (θ / 2) ^ 3) := by
    rw [h7]
    have h9 : sin (θ / 2) * (2 * (1 - sin (θ / 2) ^ 2)) = 2 * sin (θ / 2) - 2 * (sin (θ / 2) ^ 3) := by
      ring_nf
    linarith [h9]

  rw [h8]

  have h9 : sin (θ / 2) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith [Real.pi_gt_three, h2]

  nlinarith [sq_nonneg ((sin (θ / 2)) ^ 2 - 1 / 3), sq_nonneg (sin (θ / 2) - Real.sqrt 3 / 3), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num ), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          sq_nonneg ((sin (θ / 2)) ^ 2 - 1 / 3), 
          sq_nonneg ((sin (θ / 2)) ^ 2 - 1 / 3), 
          Real.sqrt_nonneg 3, 
          sq_nonneg (sin (θ / 2) - Real.sqrt 3 / 3), 
          mul_pos h9 (show 0 < Real.sqrt 3 by positivity), 
          Real.sqrt_nonneg 3, 
          sq_nonneg (Real.sqrt 3 ^ 2 - 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
          ]