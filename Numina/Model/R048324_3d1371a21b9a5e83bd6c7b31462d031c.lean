import Mathlib

open Real

theorem algebra_155086 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ x, a^(2*x) + a^x * b^x = b^(2*x)) :
    a = b ^ ((log (1 + sqrt 5) - log 2) / (log b - log a)) := by
  have h0 := h 0
  norm_num at h0
  all_goals linarith