import Mathlib

theorem number_theory_161133 (x y : ℤ) (h : x^2 + 15 = y^2) :
    (y - x = 1 ∧ y + x = 15) ∨ (y - x = 15 ∧ y + x = 1) ∨
    (y - x = 3 ∧ y + x = 5) ∨ (y - x = 5 ∧ y + x = 3) ∨
    (y - x = -1 ∧ y + x = -15) ∨ (y - x = -15 ∧ y + x = -1) ∨
    (y - x = -3 ∧ y + x = -5) ∨ (y - x = -5 ∧ y + x = -3) := by

  have h1 : (y - x) * (y + x) = 15 := by
    nlinarith

  have h2 : (y - x) ∣ 15 := by
    use (y + x)
    all_goals
      nlinarith

  have h3 : (y - x) ≤ 15 := by
    apply Int.le_of_dvd (by norm_num) h2
  have h4 : (y - x) ≥ -15 := by
    have h5 : -(y - x) ∣ 15 := by 
      exact Int.neg_dvd.2 h2
    have h6 : -(y - x) ≤ 15 := by 
      apply Int.le_of_dvd (by norm_num) h5
    linarith

  interval_cases h5 : y - x <;> omega