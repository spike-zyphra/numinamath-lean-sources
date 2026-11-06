import Mathlib

theorem algebra_297158 {x y : ℕ} (hx : x * 40 ≤ 800) (hy : y * 20 ≤ 1000)
    (hxy : x * 50 + 4 = y * 50) :
    x = 9 ∧ y = 1 ∨ x = 15 ∧ y = 4 ∨ x = 20 ∧ y = 10 := by 
  omega