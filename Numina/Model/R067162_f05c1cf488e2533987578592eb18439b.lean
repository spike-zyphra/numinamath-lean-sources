import Mathlib

theorem algebra_202921 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₀ : a * 4 - b * 4 = 12) (h₁ : a ^ 2 - b ^ 2 = 69) :
    a ^ 2 = 169 := by
  have h2 : a - b = 3 := by
    linarith
  have h3 : a + b = 23 := by
    have h4 : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    rw [h4] at h₁
    rw [h2] at h₁
    linarith
  have ha_eq : a = 13 := by
    linarith [h2, h3]
  rw [ha_eq]
  norm_num