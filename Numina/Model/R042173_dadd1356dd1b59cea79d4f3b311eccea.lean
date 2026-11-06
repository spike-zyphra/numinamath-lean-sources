import Mathlib

theorem algebra_176178 {a : ℤ → ℤ} (ha : ∀ t, a t = t ^ 2 - 5 * t + 6) :
    ∀ t, ∃ u v, a t - a u = a u - a v := by
  intro t
  use 5 - t
  use t
  have h1 : a t = t^2 -5*t +6 := by
    apply ha
  have h2 : a (5 - t) = (5 - t)^2 -5*(5 - t) +6 := by
    apply ha
  have h3 : a (5 - t) = t^2 - 5 * t + 6 := by
    rw [h2]
    ring
  have h4 : a t = a (5 - t) := by
    linarith [h1, h3]
  rw [h4]
  all_goals
    linarith [h1, h3, h4]