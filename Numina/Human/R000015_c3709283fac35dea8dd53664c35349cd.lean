import Mathlib

open Real

lemma aux_4027 (a : ℝ) : logb 4 a = logb 2 a / 2 := by
  field_simp [logb]
  left
  rw [mul_comm, show (4 : ℝ) = 2 ^ 2 by norm_num, eq_comm]
  exact log_pow 2 2

lemma aux1' (a : ℝ) : logb 8 a = logb 2 a / 3 := by
  field_simp [logb]
  left
  rw [mul_comm, show (8 : ℝ) = 2 ^ 3 by norm_num, eq_comm]
  exact log_pow 2 3

/- The number \( x \) is such that \( \log _{2}\left(\log _{4} x\right) + \log _{4}\left(\log _{8} x\right) + \log _{8}\left(\log _{2} x\right) = 1 \). Find the value of the expression \( \log _{4}\left(\log _{2} x\right) + \log _{8}\left(\log _{4} x\right) + \log _{2}\left(\log _{8} x\right) \). If necessary, round your answer to the nearest 0.01.-/
theorem algebra_4027 {x : ℝ} (hx : logb 2 x ≠ 0) (h : logb 2 (logb 4 x) + logb 4 (logb 8 x) + logb 8 (logb 2 x) = 1) :
    logb 4 (logb 2 x) + logb 8 (logb 4 x) + logb 2 (logb 8 x) = 5 / 3 - logb 2 3 / 2 := by
  -- use `log4 a = log2 a / 2` and `log8 a = log2 a / 3` to simplify
  simp only [aux_4027, aux1'] at *
  -- use `log2 (x/y) = log2 x - log2 y` to simplify
  repeat rw [logb_div hx (by norm_num)] at *
  -- transform into linear equation of `y = log2 (log2 x)`
  set y := logb 2 (logb 2 x)
  rw [logb_self_eq_one (by norm_num)] at h
  -- solution of above linear equation is `y=(12 + 2log2 3)/11`
  have : y = (12 + 3 * logb 2 3) / 11 := by linarith
  rw [this, logb_self_eq_one (by norm_num)]
  ring
