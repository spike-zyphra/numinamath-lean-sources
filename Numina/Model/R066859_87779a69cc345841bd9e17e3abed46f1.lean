import Mathlib

theorem algebra_212607 (total_people : ℕ) (h₀ : total_people ≠ 0)
    (h₁ : (90 + 9) * total_people = 180 * (total_people - 90)) (h₂ : (105 / 100) * total_people = (90 / 100) * total_people + 9) :
    total_people = 120 := by 
  omega