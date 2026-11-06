import Mathlib

theorem algebra_194469 (x : ℕ) (hx : x < 10) (h : (x + 10) * (1 + 10 / x : ℝ) = 72) :
    x = 2 := by
  have h1 : x > 0 := by
    by_contra h2
    push_neg at h2
    have h3 : x = 0 := by
      omega
    rw [h3] at h
    norm_num at h
  interval_cases x <;> norm_num at h <;> all_goals linarith