import Mathlib
theorem algebra_608139 (f : ℚ → ℝ) (hf : ∀ x : ℚ, x ≠ 0 ∧ x ≠ 1 → f x + f (1 - 1 / x) = Real.log |x|) : f 2007 = Real.log (2007 / 2006):= by
  have h1 := hf 2007 (by norm_num)
  have h2 := hf (2006 / 2007) (by norm_num)
  have h3 := hf (-1 / 2006) (by norm_num)
  norm_num [Real.log_div, Real.log_abs] at h1 h2 h3 ⊢
  linarith