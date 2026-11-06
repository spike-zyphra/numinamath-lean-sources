import Mathlib

theorem algebra_162
  (a b c : ℝ)
  (h₀ : 2 * a + 13 * b + 3 * c = 90)
  (h₁ : 3 * a + 9 * b + c = 72) :
  (3 * b + c) / (a + 2 * b) = 1 := by
  have h2 : a + 2 * b = 18 := by
    have hc : c = 72 - 3 * a - 9 * b := by linarith
    rw [hc] at h₀
    linarith

  have hc : 3 * b + c = 18 := by
    have hc' : c = 72 - 3 * a - 9 * b := by linarith
    rw [hc']
    linarith [h2]

  have h3 : a + 2 * b ≠ 0 := by
    linarith [h2]

  field_simp [h3]
  linarith [hc, h2]