import Mathlib

theorem algebra_187562 {f : ℝ → ℝ} (h : ∀ x y, f (x / y) = f x - f y)
    (h' : ∃ x, x > 1 ∧ f x > 0) :
    {x | f x + f (x + 1 / 2) < 0} = {x | (1 - Real.sqrt 17) / 4 < x ∧ x < 0} := by

  have h1 : f 0 = 0 := by
    specialize h 0 0
    simp at h
    linarith
  have h2 : ∀ x : ℝ, f x = 0 := by
    intro x
    specialize h x 0
    simp at h
    linarith [h1, h]
  rcases h' with ⟨x, hx1, hfx⟩
  have h3 : f x = 0 := h2 x
  linarith [h3, hfx]