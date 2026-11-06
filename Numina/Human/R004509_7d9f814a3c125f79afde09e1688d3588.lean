import Mathlib

theorem algebra_277170 {x : ℝ} (hx : x > 0) (h : 24000 / x = 36000 / (x - 24000)) :
    x = 28800 := by
  have hx2 : x - 24000 ≠ 0 := by
    by_contra h1
    have : x = 24000 := by linarith
    rw [this] at h
    norm_num at h

  field_simp [hx2, show x ≠ 0 by linarith] at h

  nlinarith