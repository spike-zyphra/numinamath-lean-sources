import Mathlib

theorem algebra_244065 (f : ℝ → ℝ) (h : ∀ x y, f (x + 2 * y) - f (3 * x - 2 * y) = 2 * y - x) :
    ∀ t, f (5 * t) - f t = 4 * (f (4 * t) - f (3 * t)) := by
  intro t
  have eq1 : f (5 * t) - f t = 2 * t := by
    specialize h (3 * t / 2) (7 * t / 4)
    have h1 : (3 * t / 2 : ℝ) + 2 * (7 * t / 4 : ℝ) = 5 * t := by
      ring_nf
    have h2 : 3 * (3 * t / 2 : ℝ) - 2 * (7 * t / 4 : ℝ) = (t : ℝ) := by
      ring_nf
    rw [h1, h2] at h
    linarith
  have eq2 : f (4 * t) - f (3 * t) = t / 2 := by
    specialize h (7 * t / 4) (9 * t / 8)
    have h3 : (7 * t / 4 : ℝ) + 2 * (9 * t / 8 : ℝ) = 4 * t := by
      ring_nf
    have h4 : 3 * (7 * t / 4 : ℝ) - 2 * (9 * t / 8 : ℝ) = 3 * t := by
      ring_nf
    rw [h3, h4] at h
    linarith
  linarith [eq1, eq2]