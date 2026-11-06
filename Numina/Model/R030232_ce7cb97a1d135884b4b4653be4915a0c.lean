import Mathlib

open Real

theorem algebra_12660 {a : ℝ} (ha : a > 0) (f : ℝ → ℝ)
    (hf : ∀ x, f x = log (sqrt (1 + a^2 * x^2) - a * x) + 1) :
    f (log a) + f (log (1 / a)) = 2 := by
  have h1 : log (1 / a) = - log a := by 
    field_simp [log_div, log_one]
  rw [h1]
  have h2 : f (log a) = log (sqrt (1 + a^2 * (log a)^2) - a * (log a)) + 1 := hf (log a)
  have h3 : f (-log a) = log (sqrt (1 + a^2 * (-log a)^2) - a * (-log a)) + 1 := hf (-log a)
  rw [h2, h3]
  have h4 : 1 + a^2 * (-log a)^2 = 1 + a^2 * (log a)^2 := by
    ring_nf
  have h5 : sqrt (1 + a^2 * (-log a)^2) = sqrt (1 + a^2 * (log a)^2) := by
    rw [h4]
  have h6 : log (sqrt (1 + a^2 * (-log a)^2) - a * (-log a)) = log (sqrt (1 + a^2 * (log a)^2) + a * (log a)) := by
    rw [h5]
    ring_nf
  have h7 : log (sqrt (1 + a^2 * (log a)^2) - a * (log a)) + log (sqrt (1 + a^2 * (log a)^2) + a * (log a)) = 0 := by
    have h8 : sqrt (1 + a^2 * (log a)^2) ^ 2 = 1 + a^2 * (log a)^2 := by
      rw [Real.sq_sqrt]
      positivity
    have h9 : (sqrt (1 + a^2 * (log a)^2) - a * (log a)) * (sqrt (1 + a^2 * (log a)^2) + a * (log a)) = 1 := by
      nlinarith [h8]
    have h10 : log ((sqrt (1 + a^2 * (log a)^2) - a * (log a)) * (sqrt (1 + a^2 * (log a)^2) + a * (log a))) = log (sqrt (1 + a^2 * (log a)^2) - a * (log a)) + log (sqrt (1 + a^2 * (log a)^2) + a * (log a)) := by
      rw [log_mul]
      all_goals nlinarith [Real.sqrt_pos.mpr (show 0 < (1 + a^2 * (log a)^2 : ℝ) by positivity)]
    have h11 : log ((sqrt (1 + a^2 * (log a)^2) - a * (log a)) * (sqrt (1 + a^2 * (log a)^2) + a * (log a))) = log 1 := by
      rw [h9]
    have h12 : log 1 = 0 := by
      simp
    linarith [h10, h11, h12]
  rw [h6]
  linarith [h7]