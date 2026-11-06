import Mathlib

open Real

theorem algebra_184223 {t : ℝ} (ht : t > 0) :
    (2 * sqrt (1 + (1 / 4) * (sqrt (1 / t) - sqrt t) ^ 2)) /
    (sqrt (1 + (1 / 4) * (sqrt (1 / t) - sqrt t) ^ 2) -
     (1 / 2) * (sqrt (1 / t) - sqrt t)) = 1 + 1 / t := by 
  have h1 : sqrt (1 / t) = 1 / sqrt t := by
    have h3 : sqrt (1 / t) = 1 / sqrt t := by
      have h4 : sqrt (1 / t) = Real.sqrt 1 / Real.sqrt t := by
        rw [← Real.sqrt_div (by positivity)]
      have h5 : Real.sqrt 1 = (1 : ℝ) := Real.sqrt_one
      rw [h5] at h4
      linarith
    exact h3
  have h3 : sqrt (1 / t) * sqrt t = 1 := by
    rw [h1]
    field_simp [show sqrt t > 0 by positivity]
  have h6 : 1 + (1 / 4) * (sqrt (1 / t) - sqrt t) ^ 2 = ((sqrt (1 / t) + sqrt t) ^ 2) / 4 := by
    have h7 : sqrt (1 / t) * sqrt t = 1 := h3
    nlinarith [sq_nonneg (sqrt (1 / t) - sqrt t), sq_nonneg (sqrt (1 / t) + sqrt t), 
          Real.sqrt_nonneg (1 / t), Real.sqrt_nonneg t, 
          Real.sq_sqrt (show 0 ≤ (1 / t : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ t by positivity)]
  have h13 : sqrt (1 + (1 / 4) * (sqrt (1 / t) - sqrt t) ^ 2) = (sqrt (1 / t) + sqrt t) / 2 := by 
    have h14 : (1 + (1 / 4) * (sqrt (1 / t) - sqrt t) ^ 2) = ((sqrt (1 / t) + sqrt t) ^ 2) / 4 := h6
    rw [h14]
    have h15 : sqrt (((sqrt (1 / t) + sqrt t) ^ 2) / 4) = (sqrt (1 / t) + sqrt t) / 2 := by 
      have h16 : ((sqrt (1 / t) + sqrt t) ^ 2) / 4 = (( (sqrt (1 / t) + sqrt t) / 2 ) ^ 2) := by 
        ring_nf 
      rw [h16] 
      have h17 : sqrt ( ((sqrt (1 / t) + sqrt t) / 2 ) ^ 2 ) = (sqrt (1 / t) + sqrt t) / 2 := by 
        apply Real.sqrt_sq 
        positivity 
      linarith 
    exact h15 
  have h18 : (2 * sqrt (1 + (1 / 4) * (sqrt (1 / t) - sqrt t) ^ 2)) =
      (sqrt (1 / t) + sqrt t) := by 
    rw [h13]
    ring_nf 
  have h19 : (sqrt (1 + (1 / 4) * (sqrt (1 / t) - sqrt t) ^ 2) -
      (1 / 2) * (sqrt (1 / t) - sqrt t)) = Real.sqrt t := by 
    rw [h13]
    nlinarith [Real.sqrt_nonneg (1 / t), Real.sqrt_nonneg t]
  rw [h18, h19]
  have h110 : sqrt (1 / t) / sqrt t = 1 / t := by 
    rw [h1]
    field_simp [show sqrt t > 0 by positivity, Real.sq_sqrt (show 0 ≤ t by positivity)]
  have h111 : (sqrt (1 / t) + sqrt t) / Real.sqrt t = 1 + 1 / t := by 
    have h112 : (sqrt (1 / t) + sqrt t) / Real.sqrt t = (sqrt (1 / t) / sqrt t) + (sqrt t / sqrt t) := by 
      ring_nf 
    rw [h112]
    have h113 : sqrt t / sqrt t = 1 := by 
      have h114 : sqrt t > 0 := by positivity 
      field_simp 
    rw [h113]
    have h115 : sqrt (1 / t) / sqrt t = 1 / t := h110
    rw [h115]
    all_goals ring 
  exact h111