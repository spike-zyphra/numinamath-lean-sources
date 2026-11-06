import Mathlib

theorem algebra_16796 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₀ : 4 * a = 24) (h₁ : b^2 = (1 / 4) * a^2) :
    4 * b = 12 := by
  have ha6 : a = 6 := by
    linarith
  rw [ha6] at h₁
  have h2 : b^2 = 9 := by
    nlinarith
  have hb3 : b = 3 := by
    nlinarith [sq_nonneg (b - 3), h2, hb]
  linarith [hb3]