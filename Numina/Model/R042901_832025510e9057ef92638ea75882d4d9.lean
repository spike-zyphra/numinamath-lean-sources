import Mathlib

theorem algebra_253719 (f : ℝ → ℝ) : (∀ x y, f (x * y + 1) = x * f y + 2) ↔ ∀ x, f x = 2 * x := by
  constructor
  · -- Assume functional equation holds prove f(x) = 2x
    intro h
    have h1 : f 1 = 2 := by
      specialize h 0 0
      norm_num at h
      linarith
    -- We compute $f(0)$ by setting $x = 1$, $y = 0$ in the functional equation.
    have h0 : f 0 = 0 := by
      have h2 := h 1 0
      norm_num at h2
      linarith [h1]
    have h3 : ∀ (y : ℝ), f (y + 1) = f y + 2 := by 
      intro y
      specialize h 1 y
      norm_num at h
      linarith
    have h5 : ∀ x, f (x + 1) = 2 * x + 2 := by
      intro x
      specialize h x 1
      norm_num at h
      rw [h1] at h
      linarith
    intro x
    have eq1 := h3 x
    have eq2 := h5 x
    linarith
  · -- Show that f(x) = 2x satisfies the functional equation
    intro h x y
    have hfx : ∀ (x : ℝ), f x = 2 * x := h
    have h1 : f (x * y + 1) = 2 * (x * y + 1) := by
      apply hfx
    have h2 : f y = 2 * y := by
      apply hfx
    rw [h1, h2]
    ring