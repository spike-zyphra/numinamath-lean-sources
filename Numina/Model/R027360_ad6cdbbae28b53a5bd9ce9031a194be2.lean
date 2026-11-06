import Mathlib

theorem algebra_50374 {f : ℝ → ℝ → ℝ}
    (h : ∀ x y z, f x y + f y z + f z x = 0) :
    ∃ g : ℝ → ℝ, ∀ x y, f x y = g x - g y := by
  use fun x => f x (0 : ℝ)
  intro x y
  have h1 : f x x = 0 := by
    specialize h x x x
    norm_num at h ⊢
    linarith

  have h3 : f (0 : ℝ) x = -f x (0 : ℝ) := by
    have h4 := h x (0 : ℝ) x
    norm_num [show f x x = 0 by linarith [h1]] at h4 ⊢
    linarith

  have h4 := h x y (0 : ℝ)
  simp [show f (0 : ℝ) x = -f x (0 : ℝ) by linarith [h3]] at h4 ⊢
  linarith [h4]