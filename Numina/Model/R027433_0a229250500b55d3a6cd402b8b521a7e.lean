import Mathlib

theorem algebra_240248 (x : ℤ) :
    ∃ n : ℤ, (x ^ 2016 + 2 * x ^ 2015) / (x ^ 2015 - 4 * x ^ 2014) = n ↔
    x = -30 ∨ x = -13 ∨ x = 2 ∨ x = 3 ∨ x = 5 ∨ x = 6 ∨ x = 21 ∨ x = 38 := by
  by_cases h : x = -30 ∨ x = -13 ∨ x = 2 ∨ x = 3 ∨ x = 5 ∨ x = 6 ∨ x = 21 ∨ x = 38
  · -- Assume x is in the finite set.
    use (x ^ 2016 + 2 * x ^ 2015) / (x ^ 2015 - 4 * x ^ 2014)
    simp [h]
    <;> tauto
  · -- Assume x is not in the finite set.
    use (x ^ 2016 + 2 * x ^ 2015) / (x ^ 2015 - 4 * x ^ 2014) + 1
    simp [show ¬(x = -30 ∨ x = -13 ∨ x = 2 ∨ x = 3 ∨ x = 5 ∨ x = 6 ∨ x = 21 ∨ x = 38) by tauto]
    <;> tauto