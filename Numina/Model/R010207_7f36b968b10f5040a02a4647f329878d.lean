import Mathlib

theorem algebra_10920
    (t : ℝ)
    (h : ∃ x y, x = t ∧ y = 5 ∧ (x - 0) * (0 - 3) = (y - 3) * (-8 - 0)) :
    t = 16 / 3 := by 
  rcases h with ⟨x, y, hx, hy, hline⟩
  rw [hx, hy] at hline
  linarith