import Mathlib

theorem algebra_298629 {n : ℤ} (hn : n ≠ 0) (x : ℝ)
    (h : x = (1991 ^ ((1 : ℝ) / n) - 1991 ^ (-(1 : ℝ) / n)) / 2) :
    (x - Real.sqrt (1 + x ^ 2)) ^ n = (-1) ^ n / 1991 := by
  have h10 : (1991 : ℝ) ^ ((1 : ℝ) / n) * (1991 : ℝ) ^ (-(1 : ℝ) / n) = 1 := by
    have h6 : (1991 : ℝ) ^ ((1 : ℝ) / n) * (1991 : ℝ) ^ (-(1 : ℝ) / n) = (1991 : ℝ) ^ (0 : ℝ) := by
      rw [← Real.rpow_add]
      ring
      all_goals linarith
    have h7 : (1991 : ℝ) ^ (0 : ℝ) = 1 := by
      norm_num
    rw [h7] at h6
    linarith [h6]

  have h14 : Real.sqrt (1 + x ^ 2) = ( (1991 : ℝ) ^ ((1 : ℝ) / n) + (1991 : ℝ) ^ (-(1 : ℝ) / n) ) / 2 := by
    have h7 : (( (1991 : ℝ) ^ ((1 : ℝ) / n) + (1991 : ℝ) ^ (-(1 : ℝ) / n) ) / 2 ) ^ 2 = 1 + x ^ 2 := by
      rw [h]
      have h100 : (( (1991 : ℝ) ^ ((1 : ℝ) / n) + (1991 : ℝ) ^ (-(1 : ℝ) / n) ) / 2 ) ^ 2 =
          (( (1991 : ℝ) ^ ((1 : ℝ) / n) ) ^ 2 + (( (1991 : ℝ) ^ (-(1 : ℝ) / n) ) ) ^ 2 + 2 * ( (1991 : ℝ) ^ ((1 : ℝ) / n) * (1991 : ℝ) ^ (-(1 : ℝ) / n) )) / 4 := by
        ring_nf
      rw [h100]
      have h101 : ( (1991 : ℝ) ^ ((1 : ℝ) / n) ) * ( (1991 : ℝ) ^ (-(1 : ℝ) / n) ) = 1 := h10
      rw [h101]
      nlinarith [show (0 : ℝ) < (1991 : ℝ) by norm_num]
    have h8' : (( (1991 : ℝ) ^ ((1 : ℝ) / n) + (1991 : ℝ) ^ (-(1 : ℝ) / n) ) / 2 ) ≥ 0 := by
      have h4 : (1991 : ℝ) ^ ((1 : ℝ) / n) > 0 := by positivity
      have h5 : (1991 : ℝ) ^ (-(1 : ℝ) / n) > 0 := by positivity
      positivity
    have h2 : Real.sqrt (1 + x ^ 2) = ( (1991 : ℝ) ^ ((1 : ℝ) / n) + (1991 : ℝ) ^ (-(1 : ℝ) / n) ) / 2 := by
      have h3 : Real.sqrt (1 + x ^ 2) = Real.sqrt ((( (1991 : ℝ) ^ ((1 : ℝ) / n) + (1991 : ℝ) ^ (-(1 : ℝ) / n) ) / 2 ) ^ 2) := by
        rw [show 1 + x ^ 2 = (( (1991 : ℝ) ^ ((1 : ℝ) / n) + (1991 : ℝ) ^ (-(1 : ℝ) / n) ) / 2 ) ^ 2 by linarith [h7] ]
      rw [h3]
      rw [Real.sqrt_sq (show (( (1991 : ℝ) ^ ((1 : ℝ) / n) + (1991 : ℝ) ^ (-(1 : ℝ) / n) ) / 2 ) ≥ 0 by linarith [h8'] )]
    linarith

  have h9 : x - Real.sqrt (1 + x ^ 2) = - ( (1991 : ℝ) ^ (-(1 : ℝ) / n) ) := by
    rw [h14, h]
    ring

  rw [h9]

  have h11 : (- ( (1991 : ℝ) ^ (-(1 : ℝ) / n) )) ^ n = (-1 : ℝ) ^ n * ( (1991 : ℝ) ^ (-(1 : ℝ) / n) ) ^ n := by
    have h102 : ((- ( (1991 : ℝ) ^ (-(1 : ℝ) / n) )) : ℝ) = (-1) * ((1991 : ℝ) ^ (-(1 : ℝ) / n)) := by ring
    rw [h102]
    rw [mul_zpow]
    all_goals norm_num

  rw [h11]

  have h13 : ( (1991 : ℝ) ^ (-(1 : ℝ) / n) ) ^ n = (1991 : ℝ) ^ (-1 : ℝ) := by
    rw [← Real.rpow_intCast]
    rw [← Real.rpow_mul]
    field_simp
    all_goals positivity

  rw [h13]

  have h140 : (1991 : ℝ) ^ (-1 : ℝ) = 1 / 1991 := by
    norm_num

  rw [h140]

  all_goals ring