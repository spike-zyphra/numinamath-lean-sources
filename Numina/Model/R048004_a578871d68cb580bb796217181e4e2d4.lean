import Mathlib

theorem algebra_123417 (f : ℝ → ℝ) :
    (∀ x y, f (x - f y) = 1 - x - y) ↔ ∀ x, f x = (1 / 2) - x := by
  constructor
  · -- Assume ∀ x y, f (x - f y) = 1 - x - y, prove ∀ x, f x = (1 / 2) - x
    intro h 
    have h1 : ∀ y, f 0 = 1 - f y - y := by 
      intro y
      specialize h (f y) y 
      norm_num at h 
      exact_mod_cast h 
    have h2 : ∀ y, f y = 1 - f 0 - y := by
      intro y 
      have eq1 := h1 y 
      linarith 
    have h3 : f 0 = 1 / 2 := by
      have h4 := h1 0 
      norm_num at h4 
      linarith
    intro x 
    specialize h2 x
    rw [h3] at h2 
    linarith 
  · -- Assume ∀ x, f x = (1 / 2) - x, prove ∀ x y, f (x - f y) = 1 - x - y
    intro h x y 
    have h1 : f y = (1 / 2) - y := h y 
    have h3 : f (x - f y) = (1 / 2) - (x - f y) := by 
      apply h 
    rw [h3] 
    rw [h1] 
    ring_nf