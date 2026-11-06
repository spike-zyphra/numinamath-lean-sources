import Mathlib

theorem algebra_6040 {x y : ℕ} (hy : y > x) (h : 3 * x + 10 * y = 99) :
    x = 3 ∧ y = 9 := by 
  have h1 : x ≤ 33 := by 
    omega
  have h2 : y ≤ 9 := by 
    omega
  have h3 : x = 3 := by
    omega
  have h4 : y = 9 := by
    omega
  exact ⟨h3, h4⟩