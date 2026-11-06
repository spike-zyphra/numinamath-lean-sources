import Mathlib

theorem algebra_10259 (x y r: ℝ) (hy : y = 0) (hr : 0 < r)
    (h : (x - 0)^2 + (y - 4)^2 = r^2 ∧ (x - 1)^2 + (y - 3)^2 = r^2) :
    r = 5 := by
  rcases h with ⟨h1, h2⟩
  rw [hy] at h1 h2
  have eq1 : x^2 + 16 = r^2 := by
    nlinarith
  have eq2 : (x - 1)^2 + 9 = r^2 := by
    nlinarith
  have eq3 : x^2 + 16 = (x - 1)^2 + 9 := by
    linarith [eq1, eq2]
  have hx : x = -3 := by
    nlinarith [eq3]
  have hr2 : r^2 = 25 := by
    rw [hx] at eq1
    nlinarith
  have hr5 : r = 5 := by
    nlinarith [hr]
  exact hr5