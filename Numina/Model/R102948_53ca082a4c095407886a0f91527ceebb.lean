import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_169883 {f : ℝ → ℝ} (hf : Even f)
  (h : ∀ x, f (x - sqrt 2 / 2) = f (x + sqrt 2 / 2)) :
  ∀ x, f (x - sqrt 2) = f (x + sqrt 2) := by
  intro x
  have h1 : f x = f (x + sqrt 2) := by
    specialize h (x + sqrt 2 / 2)
    have h_left : (x + sqrt 2 / 2) - sqrt 2 / 2 = x := by ring
    have h_right : (x + sqrt 2 / 2) + sqrt 2 / 2 = x + sqrt 2 := by ring
    rw [h_left] at h
    rw [h_right] at h
    simpa using h
  have h2 : f (x - sqrt 2) = f x := by
    specialize h (x - sqrt 2 / 2)
    have h_left : (x - sqrt 2 / 2) - sqrt 2 / 2 = x - sqrt 2 := by ring
    have h_right : (x - sqrt 2 / 2) + sqrt 2 / 2 = x := by ring
    rw [h_left] at h
    rw [h_right] at h
    simpa using h
  linarith [h1, h2]