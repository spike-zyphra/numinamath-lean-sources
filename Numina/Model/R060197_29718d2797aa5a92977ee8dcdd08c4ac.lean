import Mathlib

theorem algebra_256202 {X Y : ℕ} (hX : X + 2 * Y = 30) :
    X * Y ≤ 112 := by 
  have h1 : X ≤ 30 := by 
    omega
  have h2 : Y ≤ 15 := by 
    omega
  interval_cases Y <;> omega