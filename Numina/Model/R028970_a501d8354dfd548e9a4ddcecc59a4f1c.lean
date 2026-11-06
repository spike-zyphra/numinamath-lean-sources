import Mathlib

theorem number_theory_83678 {x y : ℤ} (hx : x > 0) (hy : y > 0)
    (h1 : x * y + x + y = 71) (h2 : x ^ 2 * y + x * y ^ 2 = 880) :
    (x = 11 ∧ y = 5) ∨ (x = 5 ∧ y = 11) := by
  have h3 : x ≤ 35 := by 
    nlinarith [h1]
  have h4 : y ≤ 35 := by 
    nlinarith [h1]
  interval_cases x <;> interval_cases y
    <;> omega