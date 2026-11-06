import Mathlib

theorem algebra_4088 {f : ℝ → ℝ} (hf : ContinuousAt f 0) (h : ∀ x y z, 3 * f (x + y + z) + f (x + y - z) + f (x + z - y) + f (y + z - x) = 28 * (f x + f y + f z)) :
    ∀ x, f x = 0 := by
  have h0 : f 0 = 0 := by
    have h1 := h 0 0 0
    simp at h1 
    linarith

  have h1 : ∀ a, f (-a) = 23 * f a := by
    intro a
    have h2 := h 0 0 a
    simp [show f 0 = 0 by exact h0] at h2 
    linarith

  have h2 : ∀ a, f a = 23 * f (-a) := by
    intro a
    have h3 := h 0 0 (-a)
    simp [show f 0 = 0 by exact h0] at h3 
    linarith

  have h3 : ∀ a, f a = 0 := by
    intro a
    have h4 : f a = 529 * f a := by
      have h4 : f a = 23 * f (-a) := h2 a
      have h5 : f (-a) = 23 * f a := h1 a 
      rw [h5] at h4
      linarith 
    linarith

  intro x
  exact h3 x