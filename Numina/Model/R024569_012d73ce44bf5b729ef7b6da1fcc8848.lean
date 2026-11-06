import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12006 {f : ℝ → ℝ} (hf : ∀ x, f x = log (sqrt (1 + π^2 * x^2) - π * x) + π)
    (m : ℝ) (hm : f m = 3) : f (-m) = 2 * π - 3 := by

  have h1 : f m = log (sqrt (1 + π^2 * m^2) - π * m) + π := by 
    specialize hf m 
    simpa using hf 
  have h2 : f (-m) = log (sqrt (1 + π^2 * (-m)^2) - π * (-m)) + π := by 
    specialize hf (-m) 
    simpa using hf 
  have h3 : sqrt (1 + π^2 * (-m)^2) = sqrt (1 + π^2 * m^2) := by 
    ring_nf 
  have h4 : π * (-m) = - (π * m) := by ring 
  rw [h3, h4] at h2 
  have eq1 : log (sqrt (1 + π^2 * m^2) - π * m) = 3 - π := by 
    linarith [hm, h1] 
  have h5 : log (sqrt (1 + π^2 * m^2) + π * m) = π - 3 := by 
    have h6 : (sqrt (1 + π^2 * m^2) + π * m) * (sqrt (1 + π^2 * m^2) - π * m) = 1 := by
      have h12 : sqrt (1 + π^2 * m^2) ^2 = 1 + π^2 * m^2 := by 
        rw [Real.sq_sqrt] 
        positivity 
      nlinarith [h12] 
    have h7 : log ((sqrt (1 + π^2 * m^2) + π * m) * (sqrt (1 + π^2 * m^2) - π * m)) = log (1 : ℝ) := by 
      rw [h6] 
    have h8 : log (1 : ℝ) = (0 : ℝ) := by 
      simp 
    have h9 : log ((sqrt (1 + π^2 * m^2) + π * m) * (sqrt (1 + π^2 * m^2) - π * m)) = log (sqrt (1 + π^2 * m^2) + π * m) + log (sqrt (1 + π^2 * m^2) - π * m) := by 
      rw [log_mul (by 
        have h11 : sqrt (1 + π^2 * m ^ 2) > 0 := by 
          apply Real.sqrt_pos.mpr 
          positivity 
        have h12 : π * m > -sqrt (1 + π^2 * m ^ 2) := by 
          nlinarith [Real.sqrt_nonneg (1 + π^2 * m^2), Real.sq_sqrt (show (1 + π^2 * m ^ 2 : ℝ) ≥ 0 by positivity), sq_nonneg (π * m - (-sqrt (1 + π^2 * m ^ 2))), Real.sq_sqrt (show (1 + π^2 * m ^ 2 : ℝ) ≥ 0 by positivity)]
        nlinarith 
      ) (by 
        have h13 : sqrt (1 + π^2 * m ^ 2) > 0 := by 
          apply Real.sqrt_pos.mpr 
          positivity 
        have h14 : π * m > -sqrt (1 + π^2 * m ^ 2) := by 
          nlinarith [Real.sqrt_nonneg (1 + π^2 * m^2), Real.sq_sqrt (show (1 + π^2 * m ^ 2 : ℝ) ≥ 0 by positivity), sq_nonneg (π * m - (-sqrt (1 + π^2 * m ^ 2))), Real.sq_sqrt (show (1 + π^2 * m ^ 2 : ℝ) ≥ 0 by positivity)]
        nlinarith 
      )]
    rw [h9] at h7 
    nlinarith [eq1, h8] 
  have h2' : f (-m) = log (sqrt (1 + π^2 * m^2) + π * m) + π := by 
    ring_nf at h2 ⊢ 
    all_goals linarith 
  rw [h2']
  all_goals linarith [h5]