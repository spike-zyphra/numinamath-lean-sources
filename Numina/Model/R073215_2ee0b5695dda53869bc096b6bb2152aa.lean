import Mathlib

theorem algebra_262958 {a b : ℕ} (ha : a > 0) (hb : b > 0)
    (h : a^2 + b^2 = 2120) (h' : a = b + 12) :
    a = 38 ∧ b = 26 := by
  rw [h'] at h
  have h1 : b ≤ 46 := by
    nlinarith
  interval_cases b <;> omega