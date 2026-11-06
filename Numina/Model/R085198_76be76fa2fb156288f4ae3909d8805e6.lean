import Mathlib

theorem algebra_308878 {a : ℝ} (ha : 1 < a) (m p : ℝ)
    (hm : 0 < p) (hp : p < m) (h : p + Real.logb a p = m) :
    (-p + m) + a ^ (-p + m) = m := by
  have h1 : Real.logb a p = m - p := by linarith
  have h2 : a ^ (m - p) = p := by
    have h2a : Real.logb a p = m - p := h1
    have h2b : p > 0 := by linarith
    have h2c : a ^ (Real.logb a p) = p := by
      field_simp [Real.rpow_logb, show a > 0 by linarith, show a ≠ 1 by linarith, show p > 0 by linarith]
      all_goals linarith
    rw [h2a] at h2c
    linarith

  have h3 : -p + m = m - p := by ring
  rw [h3]
  have h4 : a ^ (m - p) = p := h2
  have h5 : (m - p) + (a ^ (m - p)) = m := by
    rw [h4]
    linarith
  linarith [h5]