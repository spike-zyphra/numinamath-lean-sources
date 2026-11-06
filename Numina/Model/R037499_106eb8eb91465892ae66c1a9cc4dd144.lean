import Mathlib

theorem algebra_6868 (r : ℝ) (hr : r > 0) (h : ∀ z : ℂ, (z + 1)^5 = 32 * z^5 → z ∈ (Metric.sphere 0 r)) :
    r = 1 := by
  have h1 := h 1 (by
    norm_num [Complex.ext_iff, pow_two, pow_succ]
  )
  simp [Metric.mem_sphere] at h1
  norm_num at h1 
  all_goals linarith