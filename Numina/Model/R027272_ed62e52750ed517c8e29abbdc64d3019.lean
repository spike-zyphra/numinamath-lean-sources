import Mathlib

theorem algebra_237571 (x y : ℝ) (h : (x, y) = (-4, -2)) (t : ℝ) :
    (t + 1) * x - (2 * t + 5) * y - 6 = 0 := by
  rw [Prod.mk.inj_iff] at h
  rcases h with ⟨rfl, rfl⟩
  ring