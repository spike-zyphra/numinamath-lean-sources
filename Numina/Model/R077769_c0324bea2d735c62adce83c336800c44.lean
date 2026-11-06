import Mathlib

theorem algebra_187212 {x y z : ℝ} (h1 : 3*x+2*y+2*z=13) (h2 : 2*x+3*y+2*z=14)
    (h3 : 2*x+2*y+3*z=15) :
    x=1 ∧ y=2 ∧ z=3 := by 
  have eq4 : y = x + 1 := by
    linarith
  have eq5 : z = x + 2 := by
    linarith
  have hx : x = 1 := by
    rw [eq4, eq5] at h1
    linarith
  have hy : y = 2 := by
    rw [hx] at eq4
    linarith
  have hz : z = 3 := by
    rw [hx] at eq5
    linarith
  exact ⟨hx, hy, hz⟩