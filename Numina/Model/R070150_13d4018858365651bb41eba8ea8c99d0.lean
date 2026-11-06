import Mathlib

theorem other_198821 (v : ℝ) (h : v > 0) (h1 : 6 / v = 32 / (1.5 * v)) (h2 : 32 / (1.5 * v) = 6 / v + 2.4) :
    (32 - 6) / v = 9.57 := by
  have h4 : v ≠ 0 := by linarith
  field_simp [show v ≠ 0 by linarith] at h1 h2 ⊢
  all_goals
    linarith