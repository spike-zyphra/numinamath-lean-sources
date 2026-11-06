import Mathlib

theorem algebra_137192 (f : ℝ → ℝ) :
    (∀ x y, f (x - f y) = 1 - x - y) ↔
    ∀ x, f x = 1 / 2 - x := by
  constructor
  · -- Assume $f$ satisfies $f(x-f(y))=1-x-y$ for all $x,y$.
    intro h
    have h1 : ∀ y, f 0 = 1 - f y - y := by
      intro y
      specialize h (f y) y
      simp at h
      linarith
    -- Find f(0)
    have h2 : f 0 = 1 / 2 := by
      have eq1 := h1 0
      norm_num at eq1
      linarith
    intro x
    have eq1 := h1 x
    rw [h2] at eq1
    linarith
  · -- Assume f(x) = 1/2 - x for all x.
    intro h x y
    have h1 : f y = 1 / 2 - y := by
      apply h
    have h2 : f (x - f y) = 1 / 2 - (x - f y) := by
      apply h
    rw [h2, h1]
    ring