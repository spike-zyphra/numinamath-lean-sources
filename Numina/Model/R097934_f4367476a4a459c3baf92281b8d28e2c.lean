import Mathlib

theorem algebra_275778 (x y : ℝ) (h : ∃ c, y - x = c ∧ 3 * x + y - y = c ∧ x + 2 * y + 2 - 3 * x - y = c) :
    y - x = 6 := by 
  rcases h with ⟨c, h1, h2, h3⟩
  have h4 : c = 3 * x := by linarith
  have h5 : y = 4 * x := by 
    linarith [h1, h4]
  rw [show y = 4 * x by linarith [h5], show c = 3 * x by linarith [h4]] at h3
  have hx : x = 2 := by linarith
  have hy : y = 8 := by
    rw [show x = 2 by linarith [hx]] at h5
    linarith [h5]
  linarith [show y - x = 8 - 2 by linarith [hy, hx]]