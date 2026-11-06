import Mathlib

theorem algebra_325500 (x y : ℤ) (hx : x > 0) (hy : y > 0)
    (h : x^2 + 6 * x * y - 7 * y^2 = 2009) :
    (x = 252 ∧ y = 251) ∨ (x = 42 ∧ y = 35) ∨ (x = 42 ∧ y = 1) := by
  have h1 : (x - y) * (x + 7 * y) = 2009 := by
    nlinarith
  have h2 : (x - y) ∣ 2009 := by
    use x + 7 * y
    all_goals nlinarith
  have h3 : (x - y) ≥ 1 := by
    nlinarith
  have h4 : (x - y) ≤ 2009 := by
    apply Int.le_of_dvd (by norm_num) h2
  interval_cases h5 : (x - y) <;> omega