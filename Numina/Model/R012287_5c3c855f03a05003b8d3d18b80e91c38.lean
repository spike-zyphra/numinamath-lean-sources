import Mathlib
open Real

theorem algebra_93692 (b x a : ℝ)
  (hb : b > 1)
  (hsin : sin x > 0)
  (hcos : cos x > 0)
  (ha : logb b (sin x) = a) : logb b (cos x) = 1 / 2 * logb b (1 - b ^ (2 * a)) := by
  have h1 : sin x = b ^ a := by 
    rw [logb_eq_iff_rpow_eq] at ha 
    all_goals linarith
  have h2 : cos x ^ 2 = 1 - sin x ^ 2 := by 
    have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    nlinarith
  have h4 : cos x ^ 2 = 1 - b ^ (2 * a) := by 
    rw [h1] at h2
    have h5 : (b ^ a) ^ 2 = b ^ (2 * a) := by 
      calc 
        (b ^ a) ^ 2 = b ^ (a * 2) := by 
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring 
          all_goals linarith 
        _ = b ^ (2 * a) := by 
          ring_nf 
    rw [h5] at h2 
    linarith 
  have h6 : cos x = (1 - b ^ (2 * a)) ^ (1 / 2 : ℝ) := by 
    have h7 : cos x > 0 := hcos 
    have h8 : cos x ^ 2 = 1 - b ^ (2 * a) := h4 
    have h9 : cos x = Real.sqrt (cos x ^ 2) := by 
      rw [Real.sqrt_sq (by linarith)]
    rw [h9]
    have h10 : Real.sqrt (cos x ^ 2) = Real.sqrt (1 - b ^ (2 * a)) := by 
      rw [h8]
    rw [h10]
    have h11 : Real.sqrt (1 - b ^ (2 * a)) = (1 - b ^ (2 * a)) ^ (1 / 2 : ℝ) := by 
      rw [Real.sqrt_eq_rpow]
    rw [h11]
  rw [h6]
  have h7 : logb b ((1 - b ^ (2 * a)) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * logb b (1 - b ^ (2 * a)) := by
    rw [logb_rpow_eq_mul_logb_of_pos]
    all_goals 
      have h8 : 1 - b ^ (2 * a) > 0 := by
        have h9 : cos x ^ 2 = 1 - b ^ (2 * a) := h4
        have h10 : cos x > 0 := hcos 
        have h11 : cos x ^ 2 > 0 := by nlinarith [Real.rpow_pos_of_pos (show 0 < b by linarith) (2 * a), Real.rpow_pos_of_pos (show 0 < b by linarith) a]
        nlinarith [Real.rpow_pos_of_pos (show 0 < b by linarith) (2 * a)]
      all_goals linarith 
  rw [h7]
  all_goals linarith