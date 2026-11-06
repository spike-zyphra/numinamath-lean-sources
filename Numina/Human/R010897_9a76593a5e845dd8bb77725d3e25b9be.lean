import Mathlib

open Real

/- Find $(\log_2 x)^2$ if $\log_2 (\log_8 x) = \log_8 (\log_2 x).$ -/
theorem algebra_21388 {x : ℝ} (hx : x > 1) (h : logb 2 (logb 8 x) = logb 8 (logb 2 x)) :
    (logb 2 x)^2 = 27 := by
  -- We first show that logb 2 x is positive.
  have h₀ : 0 < logb 2 x := logb_pos (by simp) hx
  -- We then show that logb 8 z = logb 2 z / 3 for all z.
  have lem (x : ℝ) : logb 8 x = logb 2 x / 3 := by
    have h := Real.mul_logb (a := 2) (b := 8) (c := x)
    norm_num at h
    have h' : logb 2 8 = 3 := (logb_eq_iff_rpow_eq (by simp) (by simp) (by simp)).mpr (by norm_num)
    simp [← h, h']
  -- We use the lemma to rewrite the given equation.
  rw [lem, lem] at h
  cancel_denoms at h
  -- Rewrite 3 * logb 2 z as logb 2 (z ^ 3).
  nth_rw 1 [show (3 : ℝ) = (3 : ℕ) by simp, ← Real.logb_pow] at h
  -- Take the power of 2 on both sides.
  apply_fun ((2 : ℝ) ^ ·) at h
  -- Cancel 2 ^ logb 2 z on both sides.
  iterate 2 rw [Real.rpow_logb (by simp) (by simp) (by positivity)] at h
  -- Simple algebra.
  rw [show (logb 2 x / 3) ^ 3 = logb 2 x ^ 2 / 27 * logb 2 x by ring] at h
  simpa [ne_of_gt h₀, div_eq_one_iff_eq] using h
