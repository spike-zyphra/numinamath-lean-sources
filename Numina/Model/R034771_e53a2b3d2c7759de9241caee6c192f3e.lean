import Mathlib

theorem algebra_129253 (f : ℝ → ℝ) : (∀ x y, f (x + y) = f (x - y)) ↔ ∃ c, ∀ y, f y = c := by
  constructor
  · -- Assume the functional equation holds, prove f is constant
    intro h
    have h1 : ∀ y, f y = f (-y) := by
      intro y
      specialize h 0 y
      simp at h 
      simpa using h
    -- Show that f(y) = f(0) for all y
    have h2 : ∀ y, f (2 * y) = f 0 := by
      intro y
      specialize h y y
      have h3 : f (y + y) = f (y - y) := h
      have h4 : f (2 * y) = f (y + y) := by ring_nf
      have h5 : f (y - y) = f 0 := by simp at *
      rw [h4] at *
      rw [h5] at h3 
      linarith
    use f 0
    intro y
    have h3 : f y = f (-y) := h1 y
    -- Show that f(-y) = f(0)
    have h4 : f (-y) = f 0 := by
      specialize h2 ((-y) / 2)
      have h5 : f (-y) = f 0 := by
        have h6 : 2 * ((-y: ℝ)/2) = (-y: ℝ) := by ring
        rw [h6] at h2 
        linarith 
      linarith 
    linarith [h3, h4] 
  · -- Assume f is constant, prove the functional equation
    rintro ⟨c, hc⟩ 
    intro x y
    have h1 : f (x + y) = c := by 
      apply hc 
    have h2 : f (x - y) = c := by 
      apply hc 
    linarith [h1, h2]