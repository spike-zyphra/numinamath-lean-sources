import Mathlib

theorem algebra_286621 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (hxy : x = 3 * y ∧ y + 8 = x) :
    x = 12 ∧ y = 4 := by
  rcases hxy with ⟨h1, h2⟩
  have hy1 : y = 4 := by 
    linarith [h1, h2]
  have hx1 : x = 12 := by 
    rw [hy1] at h1
    linarith
  exact ⟨hx1, hy1⟩