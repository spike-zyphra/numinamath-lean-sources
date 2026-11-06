import Mathlib

theorem algebra_319506 (a : ℤ) (ha : a > 0) :
    ∃ x : ℤ, a * x ^ 2 + 2 * (2 * a - 1) * x + 4 * (a - 3) = 0 ↔
    a = 1 ∨ a = 3 ∨ a = 6 ∨ a = 10 := by
  by_cases h1 : a = 1
  · -- If a = 1, prove that x = -4 works
    use -4
    simp [h1]
    <;> omega
  by_cases h2 : a = 3
  · -- If a = 3, prove that x = 0 works
    use 0
    simp [h2]
    <;> omega
  by_cases h3 : a = 6
  · -- If a = 6, prove that x = -3 works
    use -3
    simp [h3]
    <;> omega
  by_cases h4 : a = 10
  · -- If a = 10, prove that x = -1 works
    use -1
    simp [h4]
    <;> omega
  · -- Assume a ≠ 1, 3, 6, 10, prove false
    use 0
    simp
    <;> omega