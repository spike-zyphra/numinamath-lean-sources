import Mathlib

theorem algebra_229449 {f g : ℝ → ℝ} (hf : Function.LeftInverse g f)
    (hg : Function.RightInverse g f) (hfg : ∀ x, f x + f (-x) = 2) :
    g (x - 2) + g (4 - x) = 0 := by

  have h1 : ∀ y, g (4 - y) = -g (y - 2) := by
    intro y
    have h2 : f (g (y - 2)) = y - 2 := by
      apply hg
    have h3 : f (g (4 - y)) = 4 - y := by
      apply hg
    have h4 : f (g (y - 2)) + f (-g (y - 2)) = 2 := by
      specialize hfg (g (y - 2))
      simpa using hfg
    have h5 : f (-g (y - 2)) = 4 - y := by
      linarith [h2, h4]
    have h6 : f (-g (y - 2)) = f (g (4 - y)) := by
      linarith [h3, h5]
    have h7 : -g (y - 2) = g (4 - y) := by
      apply hf.injective
      have h1 : f (-g (y - 2)) = f (g (4 - y)) := h6
      simpa using h1
    linarith
  have eq1 : g (4 - x) = -g (x - 2) := by
    specialize h1 x
    simpa using h1
  linarith [eq1]