import Mathlib

theorem number_theory_377 {r y : ℕ} (hr : r + y = 50) (hy : r + 7 * (y / 8) ≥ 90 * (r + y) / 100)
    (h : y < 8 * (r + y) / 7) : r + y ≤ 210 := by
  omega