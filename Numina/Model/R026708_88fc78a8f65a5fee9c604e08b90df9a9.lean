import Mathlib

theorem algebra_229613 {x y : ℕ} (hx : 10*x+70*y ≤ 700) (hy : 23*x+40*y ≤ 642)
    (hxy : x≥0 ∧ y≥0) :
    80*x+100*y ≤ 2180 := by
  have h1 : y ≤ 10 := by 
    omega
  have h2 : x ≤ 30 := by
    omega
  interval_cases y <;> omega