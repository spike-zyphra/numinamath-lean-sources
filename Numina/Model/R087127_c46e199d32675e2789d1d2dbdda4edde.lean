import Mathlib

theorem algebra_179632 {p v : ℝ} (hp : p = 25 / 100) (hv : v = 45 / 100)
    (h : (1 - p - v) * (1 - 27 / 100) = p * (1 - 55 / 100)) :
    p = 55 / 100 := by
  rw [hp, hv] at h
  norm_num at h ⊢
  all_goals linarith