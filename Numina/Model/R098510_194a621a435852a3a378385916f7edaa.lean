import Mathlib

theorem algebra_117255 (f : ℝ → ℝ) :
    (∀ x y, f (x - f y) = 1 - x - y) ↔ ∀ x, f x = 1 / 2 - x := by
  constructor
  · -- Assume the functional equation holds, prove f(x) = 1/2 - x
    intro h
    -- Show that f(y) = 1 - y - f(0)
    have h1 : ∀ y, f y = 1 - y - f 0 := by
      intro y
      have h2 := h (f y) y
      simp at h2
      linarith
    -- Compute f(0)
    have h2 : f 0 = 1 / 2 := by
      have h3 := h1 0
      norm_num at h3
      have h4 := h 0 0
      norm_num at h4
      linarith
    -- Finalize the proof
    intro x
    have h3 := h1 x
    rw [h2] at h3
    linarith
  · -- Assume f(x) = 1/2 - x, prove the functional equation
    intro h x y
    have hfx : ∀ x, f x = 1 / 2 - x := h
    have h1 : f y = 1 / 2 - y := hfx y
    have h2 : f (x - f y) = 1 / 2 - (x - f y) := hfx (x - f y)
    rw [h2]
    rw [show f y = 1 / 2 - y by apply hfx] -- rewrite f(y) using the given formula
    linarith