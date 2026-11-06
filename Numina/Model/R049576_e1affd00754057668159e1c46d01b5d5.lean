import Mathlib

theorem algebra_256006 {x : ℝ} (hx : x > 0) (h : 48 / (x - 2) = 48 / x + 4) :
    x = 6 := by
  have hx1 : x ≠ 0 := by linarith
  have hx2 : x - 2 ≠ 0 := by
    by_contra h'
    have : x = 2 := by linarith
    rw [this] at h
    norm_num at h
    all_goals linarith
  field_simp [hx1, hx2] at h 
  ring_nf at h
  have h1 : x ^ 2 - 2 * x - 24 = 0 := by
    nlinarith
  have h2 : (x - 6) * (x + 4) = 0 := by
    nlinarith [h1]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case h3: x - 6 = 0, so x = 6
    linarith
  · -- Case h4: x + 4 = 0, so x = -4
    nlinarith
  all_goals nlinarith