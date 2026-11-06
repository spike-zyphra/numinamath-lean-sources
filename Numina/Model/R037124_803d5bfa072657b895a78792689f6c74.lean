import Mathlib

theorem algebra_159535 {x y : ℝ} (h1 : y + Real.sqrt (y - 3 * x) + 3 * x = 12) (h2 : y^2 + y - 3 * x - 9 * x^2 = 144) :
    (x, y) = (-24, 72) ∨ (x, y) = (-4 / 3, 12) := by
  have h3 : y - 3 * x ≥ 0 := by
    by_contra h
    push_neg at h
    have h4 : Real.sqrt (y - 3 * x) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      linarith
    rw [h4] at h1
    nlinarith
  set t := Real.sqrt (y - 3 * x) with ht
  have ht2 : t ≥ 0 := by positivity
  have ht3 : t^2 = y - 3 * x := by
    have h4 : Real.sqrt (y - 3 * x) ^ 2 = y - 3 * x := Real.sq_sqrt (by linarith)
    nlinarith [ht, h4]
  have heq1 : t^2 + t + 6 * x = 12 := by
    nlinarith [h1, ht3]
  have heq2 : 6 * x * t^2 + t^4 + t^2 = 144 := by
    nlinarith [h2, ht3, heq1]
  have heq3 : 6 * x = 12 - t^2 - t := by
    nlinarith
  rw [show 6 * x = 12 - t^2 - t by nlinarith [heq3]] at heq2
  have eq1 : t^3 - 13 * t^2 + 144 = 0 := by
    nlinarith
  have eq2 : (t - 4) * (t - 12) * (t + 3) = 0 := by
    nlinarith [sq_nonneg (t ^ 2 - 16 * t + 48), sq_nonneg (t + 3)]
  cases' (mul_eq_zero.mp eq2) with h6 h7
  cases' (mul_eq_zero.mp h6) with h8 h9
  · -- t - 4 = 0
    have ht4 : t = 4 := by nlinarith
    have hx1 : x = -4 / 3 := by
      nlinarith [heq1, ht4, ht3]
    have hy1 : y = 12 := by
      nlinarith [ht3, ht4, hx1]
    right
    simp [hx1, hy1]
  · -- t - 12 = 0
    have ht12 : t = 12 := by nlinarith
    have hx2 : x = -24 := by
      nlinarith [heq1, ht12, ht3]
    have hy2 : y = 72 := by
      nlinarith [ht3, ht12, hx2]
    left
    simp [hx2, hy2]
  · -- t + 3 = 0
    have ht4 : t = -3 := by linarith
    nlinarith -- contradicts t >= 0