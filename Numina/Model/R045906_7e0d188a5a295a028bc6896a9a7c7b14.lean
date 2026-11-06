import Mathlib

theorem algebra_319397 (a : ℤ) :
    ∃ x y : ℤ, x^2 - 4 * a * x + 64 = 0 ∧ y^2 - 4 * a * y + 64 = 0 ↔
    a = 5 ∨ a = -5 ∨ a = 4 ∨ a = -4 := by
  by_cases h1 : a = 5
  · -- Assume a =5.
    use 4, 16
    simp [h1]
    <;> norm_num
    <;> norm_num
    <;> norm_num
  by_cases h2 : a = -5
  · -- Assume a =-5.
    use -4, -16
    simp [h2]
    <;> norm_num
    <;> norm_num
    <;> norm_num
  by_cases h3 : a = 4
  · -- Assume a =4.
    use 8, 8
    simp [h3]
    <;> norm_num
    <;> norm_num
    <;> norm_num
  by_cases h4 : a = -4
  · -- Assume a =-4.
    use -8, -8
    simp [h4]
    <;> norm_num
    <;> norm_num
    <;> norm_num
  · -- Assume a ≠5, a ≠-5, a ≠4, a ≠-4
    use (0 : ℤ), (0 : ℤ)
    simp at *
    all_goals omega