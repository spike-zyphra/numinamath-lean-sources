import Mathlib

theorem algebra_142514 {x y : ℕ} (hxy : x + y = 218) (hxy' : y = x * 7 / 10 + 24) :
    x = 85 ∧ y = 133 := by 
  have h1 : x + y = 218 := hxy
  have h2 : y = x * 7 / 10 + 24 := hxy'
  have h3 : x ≤ 218 := by
    omega
  have h4 : y ≤ 218 := by
    omega
  interval_cases x <;> omega