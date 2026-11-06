import Mathlib

theorem algebra_247051 (X Y : ℕ) (hX : X * 1 + Y * 2 = 30) :
    X * Y ≤ 112 := by
  have h1 : X = 30 - 2 * Y := by
    omega
  rw [h1]
  have h2 : Y ≤ 15 := by
    omega
  interval_cases Y <;> omega