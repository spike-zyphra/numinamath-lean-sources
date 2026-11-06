import Mathlib

theorem algebra_141353 {x y : ℝ} (h1 : (1/2) * (y + x/2) - (1/5) * (x + 2) = 1.1)
    (h2 : x - 2 * y + 4 = (1/4) * (2 * x + 3 * (y - 1/2))) :
    x = 5 ∧ y = 5/2 := by
  have eq1 : x + 10 * y = 30 := by
    have h1' : (1/2) * (y + x/2) - (1/5) * (x + 2) = 1.1 := h1
    ring_nf at h1'
    linarith
  have eq2 : 4 * x - 22 * y = -35 := by
    have h2' : x - 2 * y + 4 = (1/4) * (2 * x + 3 * (y - 1/2)) := h2
    ring_nf at h2'
    linarith
  have hx : x = 5 := by
    linarith [eq1, eq2]
  have hy : y = 5/2 := by
    rw [hx] at eq1
    linarith
  exact ⟨hx, hy⟩