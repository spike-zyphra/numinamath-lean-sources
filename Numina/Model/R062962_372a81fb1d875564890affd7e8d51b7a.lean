import Mathlib

open Real

theorem inequalities_171205 (x : ℝ) (hx : x > 0) :
    (0.5 : ℝ)^(2 * sqrt x) + 2 > 3 * (0.5 : ℝ)^(sqrt x) := by
  have h1 : (0.5 : ℝ) ^ (2 * sqrt x) = ((0.5 : ℝ) ^ (sqrt x)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    ring_nf
    all_goals nlinarith [show sqrt x ≥ 0 by apply sqrt_nonneg]
  rw [h1]
  have h2 : (0.5 : ℝ) ^ (sqrt x) < (1 : ℝ) := by 
    have h3 : (0.5 : ℝ) ^ (sqrt x) < (0.5 : ℝ) ^ (0 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_gt
      all_goals 
        have h6 : sqrt x > (0 : ℝ) := by
          apply Real.sqrt_pos.2
          linarith
        nlinarith [h6, show (0.5 : ℝ) < 1 by norm_num]
    have h4 : (0.5 : ℝ) ^ (0 : ℝ) = 1 := by
      simp [Real.rpow_zero]
    rw [h4] at h3
    all_goals linarith
  -- Note that (0.5)^(sqrt x) > 0.
  -- Thus multiply by upper bound and apply positivity
  nlinarith [show 0 < (0.5 : ℝ) ^ (sqrt x) by positivity, h2]