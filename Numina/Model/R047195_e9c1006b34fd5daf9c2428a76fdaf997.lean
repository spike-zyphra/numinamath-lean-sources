import Mathlib

theorem algebra_162300 (f : ℝ → ℝ) :
    (∀ x y, f (x + y) = x + f (f y)) ↔ ∀ x, f x = x := by
  constructor
  · -- Assume f satisfies the functional equation, prove f(x) = x
    intro h
    have h1 : ∀ y, f y = f (f y) := by
      intro y
      have h2 := h 0 y
      simp at h2 ⊢
      all_goals linarith
    have h3 : ∀ x, f x = x + f (f 0) := by
      intro x
      have h4 := h x 0
      simp at h4 ⊢
      all_goals linarith
    have h2 : f (f 0) = f 0 := by
      specialize h1 0
      linarith
    have h5 : ∀ x, f x = x + f 0 := by
      intro x
      specialize h3 x
      rw [h2] at h3
      linarith
    have h7 : f 0 = 0 := by
      have h8 : f (f 0) = f 0 + f 0 := by
        specialize h5 (f 0)
        simpa using h5
      have h10 : f 0 = f (f 0) := by
        specialize h1 0
        linarith
      linarith
    intro x
    specialize h5 x
    rw [h7] at h5
    linarith
  · -- Assume f(x) = x, prove the functional equation
    intro h x y
    have h1 : ∀ z, f z = z := h
    have h3 : f (x + y) = x + y := by
      apply h1
    have h4 : f (f y) = y := by
      have h5 : f y = y := by
        apply h1
      rw [h5]
      apply h1
    linarith