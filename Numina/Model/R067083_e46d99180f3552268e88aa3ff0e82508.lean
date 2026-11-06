import Mathlib

theorem algebra_284812 {x y : ℝ} (h1 : 9*x+10*y=73.8) (h2 : 17*x+6*y=69.8) :
    x=2.2 ∧ y=5.4 := by
  have hx : x = 2.2 := by
    norm_num at h1 h2
    linarith
  have hy : y = 5.4 := by
    rw [hx] at h1
    norm_num at h1
    linarith
  exact ⟨hx, hy⟩