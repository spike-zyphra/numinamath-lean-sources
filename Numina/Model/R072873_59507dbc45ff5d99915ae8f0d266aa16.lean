import Mathlib

theorem algebra_320800 (x y : ℤ) :
    x^3 + 2 * x^2 * y = 2009 ↔ (x = 1 ∧ y = 1004) ∨ (x = -1 ∧ y = 1005) ∨ (x = 7 ∧ y = 17) ∨ (x = -7 ∧ y = 24) := by
  constructor
  · -- Assume x^3 + 2 * x^2 * y = 2009, prove the four solutions
    intro h_eq
    have h1 : x^2 ∣ 2009 := by
      use x + 2 * y
      linarith
      <;> linarith
    have h2 : x^2 ≤ 2009 := by 
      exact Int.le_of_dvd (show (0 : ℤ) < 2009 by norm_num) h1
    have h3 : x^2 ≥ 0 := by nlinarith 
    have h4 : x ≤ 44 := by 
      nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
    have h5 : x ≥ -44 := by 
      nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
    interval_cases x <;> omega 
  · -- Assume one of the four solutions, prove x^3 + 2x^2y = 2009
    rintro (h | h | h | h)
    · -- Case (1, 1004)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (-1, 1005)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (7, 17)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (-7, 24)
      rcases h with ⟨rfl, rfl⟩
      norm_num