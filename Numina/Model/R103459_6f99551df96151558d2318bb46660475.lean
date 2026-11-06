import Mathlib

theorem number_theory_238823 {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x * 60 = y * 360) (hxy' : x * 60 = y * 384) :
    x = 15 ∧ y = 15 := by 
  have h1 : x = 6 * y := by
    omega
  rw [h1] at hxy'
  have h2 : y = 0 := by 
    omega
  contradiction