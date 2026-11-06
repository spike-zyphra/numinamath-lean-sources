import Mathlib

theorem algebra_311880 (a : ℤ) (ha : a > 0) :
    ∃ x : ℤ, a * x ^ 2 + 2 * (2 * a - 1) * x + 4 * (a - 3) = 0 ↔
    a = 1 ∨ a = 3 ∨ a = 6 ∨ a = 10 := by
  by_cases h1 : a = 1
  · -- If a = 1, then x = -4 is a root.
    use -4
    simp [h1]
    <;> omega
  · -- If a ≠ 1, check if a = 3
    by_cases h2 : a = 3
    · -- If a = 3, then x = 0 is a root.
      use 0
      simp [h2]
      <;> omega
    · -- If a ≠ 1, 3, check if a = 6
      by_cases h3 : a = 6
      · -- If a = 6, then x = -3 is a root.
        use -3
        simp [h3]
        <;> omega
      · -- If a ≠ 1, 3, 6, check if a = 10
        by_cases h4 : a = 10
        · -- If a = 10, then x = -1 is a root.
          use -1
          simp [h4]
          <;> omega
        · -- If a is none of 1,3,6,10 then the equation has no integer root.
          use 0
          constructor
          · -- Assume the equation is satisfied, prove a = 1 ∨ a = 3 ∨ a = 6 ∨ a = 10. This must lead to a contradiction.
            intro h
            have h5 : a = 3 := by
              nlinarith
            omega
          · -- Assume a = 1 ∨ a = 3 ∨ a = 6 ∨ a = 10, prove the equation is satisfied
            intro h
            omega