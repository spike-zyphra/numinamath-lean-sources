import Mathlib

theorem algebra_236580 {x y : ℝ} (h1 : (2 * x + 15) / 8 - (1 + 1 / 3) * (y - 1) = 2 * (5 - 2 * y) / 3)
    (h2 : (x + 5 + 3 / 4) / 2 = 3 * y + 0.125) :
    x = 1 / 2 ∧ y = 1 := by 
  have hx : x = 1 / 2 := by
    norm_num at h1 
    linarith 
  have hy : y = 1 := by
    rw [hx] at h2 
    norm_num at h2 
    linarith 
  exact ⟨hx, hy⟩