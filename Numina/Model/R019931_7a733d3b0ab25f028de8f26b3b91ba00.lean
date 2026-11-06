import Mathlib

theorem algebra_3277 {a b : ℕ} (ha : a > 0) (hb : b > 0)
    (h₀ : a^2 + b^2 = 269) (h₁ : 4 * a + 4 * b = 92) :
    max (a^2) (b^2) - min (a^2) (b^2) = 69 := by 
  have h2 : a + b = 23 := by 
    omega
  have h4 : b = 23 - a := by
    omega
  rw [h4] at h₀
  have h5 : a ≤ 23 := by
    omega
  interval_cases a <;> norm_num at h₀ h2 h4
    <;> norm_num [h4, max_eq_left, max_eq_right, min_eq_left, min_eq_right] at *
    <;> omega