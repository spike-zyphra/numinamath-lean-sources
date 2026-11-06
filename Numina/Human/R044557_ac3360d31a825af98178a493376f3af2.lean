import Mathlib

open Real Set

theorem calculus_11186 {x : ℝ} (n : ℝ) (hn : n > 0) (sinpos : 0 < sin x) (cospos : 0 < cos x)
  (h1 : logb 10 (sin x) + logb 10 (cos x) = -1) :
  logb 10 (sin x + cos x) = (logb 10 n - 1) / 2 ↔ n = 12 := by
  have h3 : sin x * cos x = 1 / 10 := by
      rw [←Real.logb_mul (by linarith) (by linarith), ←Real.logb_self_eq_one (show 10 > 1 by simp), ←Real.logb_inv] at h1
      have := Real.logb_injOn_pos (show 1 < 10 by simp) (by simp [sinpos, cospos]) (by norm_num) h1
      rw [this]
      ring
  have h4 : logb 10 (sin x + cos x) = (logb 10 12 - 1) / 2 := by
    calc
      _ = 2 *  logb 10 (sin x + cos x) / 2:= by ring
      _ = logb 10 ((sin x + cos x)^2) / 2 := by
        rw [←Real.logb_rpow_eq_mul_logb_of_pos]
        norm_cast
        linear_combination sinpos + cospos
      _ = _ := by
        rw [show (sin x + cos x) ^ 2 = (sin x) ^ 2 + (cos x) ^ 2 + 2 * sin x * cos x by ring]
        rw [Real.sin_sq_add_cos_sq, mul_assoc 2, h3]
        conv => rhs; rw [← Real.logb_self_eq_one (show 1 < 10 by norm_num), ← Real.logb_div (by norm_num) (by norm_num)]
        norm_num
  constructor
  · intro h2
    rw [h4, div_eq_div_iff two_ne_zero two_ne_zero] at h2
    apply Real.logb_injOn_pos (show 10 > 1 by norm_num)
    . simp [hn]
    . norm_num
    . linarith only [h2]
  · intro h
    rw [h4, h]
