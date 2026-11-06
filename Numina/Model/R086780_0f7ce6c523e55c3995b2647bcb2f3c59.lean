import Mathlib

theorem algebra_193768 {A Y : ℕ} (hA : A > 0) (hY : Y < 40) (h : A * Y = 4340) (h' : (A + 14) * (Y + 5) = 5520) :
    A = 124 := by 
  interval_cases Y <;> omega