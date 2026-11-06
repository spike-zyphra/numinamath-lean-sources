import Mathlib

theorem algebra_302990 (a : ℤ) :
    ∃ x : ℤ, a * x ^ 2 + 2 * a * x + a - 9 = 0 ↔ a = 1 ∨ a = 9 := by 
  by_cases h1 : a = 1
  · -- Assume a = 1
    use 2
    simp [h1]
    <;> omega
  · -- Assume a ≠ 1
    by_cases h2 : a = 9
    · -- Assume a = 9
      use 0
      simp [h2]
    · -- Assume a ≠ 1 and a ≠ 9
      use 0
      constructor
      · -- Assume a * 0 ^ 2 + 2 * a * 0 + a - 9 = 0
        intro h
        have h3 : a - 9 = 0 := by 
          nlinarith 
        have h4 : a = 9 := by linarith 
        omega 
      · -- Assume a = 1 ∨ a = 9
        intro h 
        rcases h with (h | h) 
        · -- a = 1 
          omega 
        · -- a = 9 
          omega