import Mathlib

open Real Set
open scoped Real

theorem algebra_201005 : IsGreatest {x | ∃ t : ℝ, x = sin t ^ 4 + sin t * cos t + cos t ^ 4} (9/8) := by 
  constructor
  · -- Show that 9/8 is in the set.
    use (Real.pi / 12)
    have h1 : sin (Real.pi / 12) * cos (Real.pi / 12) = 1 / 4 := by
      have h2 : sin (Real.pi / 6) = 1 / 2 := by
        rw [sin_pi_div_six]
      have h3 : sin (Real.pi / 6) = 2 * sin (Real.pi / 12) * cos (Real.pi / 12) := by 
        rw [←sin_two_mul (Real.pi / 12)]
        ring_nf
      rw [h2] at h3
      nlinarith
    have h4 : sin (Real.pi / 12) ^ 4 + sin (Real.pi / 12) * cos (Real.pi / 12) + cos (Real.pi / 12) ^ 4 = 9 / 8 := by
      have h10 : sin (Real.pi / 12) ^ 2 + cos (Real.pi / 12) ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq (Real.pi / 12)
      have h20 : sin (Real.pi / 12) ^ 4 + cos (Real.pi / 12) ^ 4 = 1 - 2 * (sin (Real.pi / 12) * cos (Real.pi / 12)) ^ 2 := by
        calc 
          sin (Real.pi / 12) ^ 4 + cos (Real.pi / 12) ^ 4 
            = (sin (Real.pi / 12) ^ 2 + cos (Real.pi / 12) ^ 2) ^ 2 - 2 * (sin (Real.pi / 12) * cos (Real.pi / 12)) ^ 2 := by 
              nlinarith
          _ = 1 ^ 2 - 2 * (sin (Real.pi / 12) * cos (Real.pi / 12)) ^ 2 := by 
              rw [h10]
          _ = 1 - 2 * (sin (Real.pi / 12) * cos (Real.pi / 12)) ^ 2 := by 
              nlinarith
      calc 
        sin (Real.pi / 12) ^ 4 + sin (Real.pi / 12) * cos (Real.pi / 12) + cos (Real.pi / 12) ^ 4 
          = (sin (Real.pi / 12) ^ 4 + cos (Real.pi / 12) ^ 4) + sin (Real.pi / 12) * cos (Real.pi / 12) := by 
            ring_nf
        _ = (1 - 2 * (sin (Real.pi / 12) * cos (Real.pi / 12)) ^ 2) + sin (Real.pi / 12) * cos (Real.pi / 12) := by 
          rw [h20]
        _ = (1 - 2 * (1 / 4) ^ 2) + (1 / 4) := by 
          rw [h1]
        _ = 9 / 8 := by 
          norm_num
    linarith [h4]
  · -- Show that 9/8 is greatest in the set.
    intro x hx
    rcases hx with ⟨t, ht⟩
    rw [ht]
    have h10 : sin t ^ 2 + cos t ^ 2 = 1 := by 
      exact Real.sin_sq_add_cos_sq t
    have h20 : sin t ^ 4 + cos t ^ 4 = 1 - 2 * (sin t * cos t) ^ 2 := by 
      calc
        sin t ^ 4 + cos t ^ 4 = (sin t ^ 2 + cos t ^ 2) ^ 2 - 2 * (sin t * cos t) ^ 2 := by 
          nlinarith
        _ = 1 ^ 2 - 2 * (sin t * cos t) ^ 2 := by 
          rw [h10]
        _ = 1 - 2 * (sin t * cos t) ^ 2 := by 
          nlinarith
    have h30 : sin t ^ 4 + sin t * cos t + cos t ^ 4 = 1 - 2 * (sin t * cos t) ^ 2 + (sin t * cos t) := by 
      nlinarith [h20]
    nlinarith [sq_nonneg (sin t * cos t - 1 / 4), sq_nonneg (sin t ^ 2 - cos t ^ 2), Real.sin_sq_add_cos_sq t, sq_nonneg (sin t - cos t), sq_nonneg (sin t), sq_nonneg (cos t)]