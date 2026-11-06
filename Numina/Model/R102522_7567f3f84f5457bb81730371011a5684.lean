import Mathlib

theorem algebra_20777 (x : ℤ) : 6500 + x - 4500 = 3400 + 2000 ↔ x = 3400 := by
  constructor
  · -- Forward direction: if 6500 + x - 4500 = 3400 + 2000 then x = 3400
    intro h
    omega
  · -- Backward direction: if x = 3400 then 6500 + x - 4500 = 3400 + 2000
    intro h
    omega