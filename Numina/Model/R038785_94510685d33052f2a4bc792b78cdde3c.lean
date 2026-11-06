import Mathlib

theorem algebra_299272 {f : ℝ → ℝ} (h1 : ∀ x, f (2 + x) = f (2 - x)) (h2 : ∀ x, f (5 - x) = f (5 + x)) :
    Function.Periodic f 6 := by
  unfold Function.Periodic
  intro x
  have h3 : ∀ y, f y = f (4 - y) := by
    intro y
    have eq1 := h1 (y - 2)
    rw [show 2 + (y - 2 : ℝ) = y by ring] at eq1
    rw [show 2 - (y - 2 : ℝ) = (4 - y : ℝ) by ring] at eq1
    linarith [eq1]
  have h4 : ∀ z, f z = f (10 - z) := by
    intro z
    have eq2 := h2 (z - 5)
    rw [show 5 - (z - 5 : ℝ) = (10 - z : ℝ) by ring] at eq2
    rw [show 5 + (z - 5 : ℝ) = z by ring] at eq2
    linarith [eq2]
  have eq4 := h4 (x + 6)
  have eq5 := h3 x
  -- Simplify the expression f(x + 6) using the relation derived from h4
  -- f(x + 6) = f(10 - (x + 6)) = f(4 - x)
  have eq6 : f (x + 6) = f (4 - x) := by
    have eq7 : f (x + 6) = f (10 - (x + 6 : ℝ)) := by
      apply h4
    have eq8 : (10 - (x + 6 : ℝ)) = (4 - x : ℝ) := by
      linarith
    rw [eq8] at eq7
    linarith [eq7]
  -- We have f(x) = f(4 - x) from h3 x
  -- And f(x + 6) = f(4 - x) from eq6
  -- Therefore f(x + 6) = f(x)
  linarith [eq5, eq6]