import Mathlib

theorem algebra_10306 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h₀ : b / a = 3) (h₁ : b = 12 - 5 * a) :
    a = 3 / 2 := by 
  have h2 : b = 3 * a := by
    have h3 : a ≠ 0 := ha
    field_simp [h3] at h₀
    linarith
  rw [h2] at h₁
  linarith