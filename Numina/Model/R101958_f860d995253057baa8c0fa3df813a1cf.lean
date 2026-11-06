import Mathlib

theorem algebra_96839 {b g : ℕ} (hb : b > 0) (hg : g > 0)
    (hj : b * b + g * g = 400 - 6) (hbg : b = g + 2) :
    b + g = 28 := by
  have eq1 : b * b + g * g = 394 := by 
    omega
  rw [hbg] at eq1
  have h1 : g ≤ 19 := by
    nlinarith 
  interval_cases g <;> omega