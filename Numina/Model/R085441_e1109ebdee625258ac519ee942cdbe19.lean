import Mathlib

theorem algebra_249950 (f : ℝ → ℝ) :
    (∀ x y, f (y - f x) = 1 - x - y) ↔ ∀ x, f x = 1 / 2 - x := by
  constructor
  · -- Assume f satisfies the functional equation, prove f(x) = 1/2 - x for all x
    intro h
    have h1 : ∀ x : ℝ, f x = 1 - x - f 0 := by
      intro x
      specialize h x (f x)
      simp at h
      linarith
    have h2 : f 0 = 1 / 2 := by
      specialize h1 0
      linarith
    intro x
    specialize h1 x
    rw [h2] at h1
    linarith
  · -- Assume f(x) = 1/2 - x for all x, prove the functional equation
    intro h
    intro x y
    rw [h (y - f x), h x]
    ring_nf