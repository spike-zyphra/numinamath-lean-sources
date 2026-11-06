import Mathlib

theorem algebra_247973 (x : ℤ) :
    ∃ k, k^2 = x^2 + 3 * x + 24 ↔ x = -23 ∨ x = -8 ∨ x = 5 ∨ x = 20 := by
  by_cases h1 : x = -23
  · -- Case 1: x = -23
    use 22
    simp [h1]
    <;> omega
  by_cases h2 : x = -8
  · -- Case 2: x = -8
    use 8
    simp [h2]
    <;> omega
  by_cases h3 : x = 5
  · -- Case 3: x = 5
    use 8
    simp [h3]
    <;> omega
  by_cases h4 : x = 20
  · -- Case 4: x = 20
    use 22
    simp [h4]
    <;> omega
  -- Case 5: x is none of the four
  push_neg at h1 h2 h3 h4
  use 0
  constructor
  · -- Forward direction: 0^2 ≠ x^2 + 3x + 24
    intro h
    have h5 : x^2 + 3 * x + 24 = 0 := by nlinarith
    have h6 : x^2 + 3 * x + 24 > 0 := by nlinarith [sq_nonneg (x + 1)]
    nlinarith
  · -- Backward direction is trivial
    rintro (r | r | r | r)
    all_goals
      contradiction