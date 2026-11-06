import Mathlib

theorem algebra_327890 (a b : ℤ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 5 * a + 7 * b = 50) :
    a * b = 15 := by
  have h2 : a ≤ 10 := by
    linarith
  have h3 : b ≤ 7 := by
    linarith
  have h4 : a ≥ 1 := by 
    linarith
  have h5 : b ≥ 1 := by 
    linarith
  interval_cases a <;> 
    interval_cases b 
    <;> omega