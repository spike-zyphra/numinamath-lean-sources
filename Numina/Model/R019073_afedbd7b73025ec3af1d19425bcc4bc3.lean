import Mathlib

theorem algebra_184639 (a : ℤ) (ha : a < 0) :
    ∃ x : ℤ, a * x ^ 2 - 2 * (a - 3) * x + (a - 2) = 0 ↔ a = -4 ∨ a = -10 := by 
  by_cases h1 : a = -4
  · -- Assume a = -4, then x=3 is a solution
    use 3
    simp [h1]
  · -- Assume a = -10
    by_cases h2 : a = -10
    · -- Assume a = -10, then x=2 is a solution
      use 2
      simp [h2]
    · -- Now a ≠ -4 and a ≠ -10
      push_neg at h1 h2
      use (0 : ℤ)
      constructor
      · -- Assume equation is satisfied: a * 0 ^ 2 - 2 * (a - 3) * 0 + (a - 2) = 0, prove a = -4 ∨ a = -10
        intro h_eq
        have eq1 : a - 2 = 0 := by
          linarith
        have eq2 : a = 2 := by linarith
        nlinarith
      · -- Assume a = -4 ∨ a = -10, prove equation
        rintro (h | h)
        · -- Case a = -4
          exfalso
          omega
        · -- Case a = -10
          exfalso
          omega