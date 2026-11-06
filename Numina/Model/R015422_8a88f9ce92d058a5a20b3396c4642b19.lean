import Mathlib

open Real Set
open scoped Real

theorem algebra_317391 (θ : ℝ) (h : sin θ + cos θ = sqrt 2) :
    (logb (1/2) (sin θ)) * (logb (1/2) (cos θ)) = 1/4 := by
  have h1 : sin θ ^ 2 + cos θ ^ 2 = 1 := by
    exact sin_sq_add_cos_sq θ
  have h5 : sin θ * cos θ = 1 / 2 := by
    have h2 : (sin θ + cos θ) ^ 2 = 2 := by
      rw [h]
      have h3 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      linarith
    have h3 : (sin θ + cos θ) ^ 2 = sin θ ^ 2 + cos θ ^ 2 + 2 * (sin θ * cos θ) := by
      ring
    rw [h3] at h2
    rw [h1] at h2
    nlinarith
  have h6 : sin θ = cos θ := by
    have h8 : (sin θ - cos θ) ^ 2 = 0 := by
      nlinarith [sq_nonneg (sin θ), sq_nonneg (cos θ), h5]
    have h9 : sin θ - cos θ = 0 := by
      rw [sq_eq_zero_iff] at h8
      linarith
    linarith
  have h7 : sin θ = sqrt 2 / 2 := by
    have h6' : sin θ = cos θ := h6
    have h2 : sin θ + cos θ = sqrt 2 := h 
    rw [show cos θ = sin θ by linarith [h6']] at h2 
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
  have h8 : cos θ = sqrt 2 / 2 := by
    have h6' : sin θ = cos θ := h6 
    have h2 : sin θ + cos θ = sqrt 2 := h 
    rw [show sin θ = cos θ by linarith [h6']] at h2 
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
  have h9 : sin θ > 0 := by 
    nlinarith [show sqrt 2 / 2 > 0 by 
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    ]
  have h10 : sin θ > 0 := h9
  have h11 : cos θ > 0 := by
    nlinarith [show sqrt 2 / 2 > 0 by 
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    ]
  have h12 : logb (1 / 2) (sin θ) = 1 / 2 := by 
    rw [show sin θ = sqrt 2 / 2 by linarith [h7]]
    -- we compute log base 1/2 of sqrt(2)/2
    -- notice that sqrt(2)/2 = (2)^(-1/2)
    have h18 : logb (1 / 2) (sqrt 2 / 2) = 1 / 2 := by 
      rw [logb]
      have h3 : log (sqrt 2 / 2) = - (log (2) / 2) := by 
        calc 
          log (sqrt 2 / 2) = log (sqrt 2) - log (2) := by 
            rw [log_div (by positivity) (by positivity)]
          _ = (1 / 2) * log 2 - log 2 := by 
            have h5 : log (sqrt 2) = (1 / 2) * log 2 := by 
              calc 
                log (sqrt 2) = log (2 ^ (1 / 2 : ℝ)) := by 
                  rw [Real.sqrt_eq_rpow]
                _ = (1 / 2 : ℝ) * log 2 := by 
                  rw [log_rpow (by norm_num)]
                  all_goals norm_num 
            rw [h5]
          _ = - (log 2 / 2) := by 
            ring_nf 
            <;> norm_num 
        <;> try linarith 
      rw [h3]
      -- we have - (log 2 / 2) / log (1 / 2)
      -- and log (1 / 2) = - log 2
      have h4 : log (1 / 2) = - log 2 := by 
        calc 
          log (1 / 2) = log 1 - log 2 := by 
            rw [log_div (by norm_num) (by norm_num)]
          _ = 0 - log 2 := by 
            simp 
          _ = - log 2 := by 
            ring 
      rw [h4]
      field_simp 
      <;> ring_nf <;> norm_num 
      <;> norm_num 
      <;> ring 
    linarith 
  have h13 : logb (1 / 2) (cos θ) = 1 / 2 := by 
    rw [show cos θ = sqrt 2 / 2 by linarith [h8]]
    -- we compute log base 1/2 of sqrt(2)/2
    -- notice that sqrt(2)/2 = (2)^(-1/2)
    have h18 : logb (1 / 2) (sqrt 2 / 2) = 1 / 2 := by 
      rw [logb]
      have h3 : log (sqrt 2 / 2) = - (log (2) / 2) := by 
        calc 
          log (sqrt 2 / 2) = log (sqrt 2) - log (2) := by 
            rw [log_div (by positivity) (by positivity)]
          _ = (1 / 2) * log 2 - log 2 := by 
            have h5 : log (sqrt 2) = (1 / 2) * log 2 := by 
              calc 
                log (sqrt 2) = log (2 ^ (1 / 2 : ℝ)) := by 
                  rw [Real.sqrt_eq_rpow]
                _ = (1 / 2 : ℝ) * log 2 := by 
                  rw [log_rpow (by norm_num)]
                  all_goals norm_num 
            rw [h5]
          _ = - (log 2 / 2) := by 
            ring_nf 
            <;> norm_num 
          _ = - (log 2 / 2) := by 
            ring 
        <;> try linarith 
      rw [h3]
      have h4 : log (1 / 2) = - log 2 := by 
        calc 
          log (1 / 2) = log 1 - log 2 := by 
            rw [log_div (by norm_num) (by norm_num)]
          _ = 0 - log 2 := by 
            simp 
          _ = - log 2 := by 
            ring 
      rw [h4]
      field_simp 
      <;> ring_nf <;> norm_num 
      all_goals norm_num 
      <;> ring 
    linarith 
  rw [h12, h13] 
  all_goals norm_num 
  all_goals norm_num 
  all_goals try ring_nf <;> norm_num 
  all_goals linarith [Real.sqrt_nonneg 2]