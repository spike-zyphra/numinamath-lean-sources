import Mathlib

theorem algebra_129293 {f : ℝ → ℝ} (h : ∀ x y, f (x * f y + y) = f (f (x * y)) + y) :
    ∀ y, f y = y := by
  have h1 : ∀ y, f y = f (f 0) + y := by
    intro y
    specialize h 0 y
    simp at h ⊢
    linarith
  have h7 : ∀ x y, x * f y = f (f 0) + x * y := by
    intro x y
    have h71 : f (x * f y + y) = f (f (x * y)) + y := h x y
    have h81 : f (x * f y + y) = f (f 0) + (x * f y + y) := by
      rw [h1 (x * f y + y)]
    have h91 : f (f (x * y)) = f (f 0) + (f (x * y)) := by
      rw [h1 (f (x * y))]
    have h101 : f (x * y) = f (f 0) + (x * y) := by
      rw [h1 (x * y)]
    rw [h81, h91, h101] at h71
    linarith
  have h8 : f (f 0) = 0 := by
    have h9 : ∀ x : ℝ, x * f 0 = f (f 0) := by
      intro x
      specialize h7 x 0 
      simp at h7 ⊢ 
      linarith 
    specialize h9 0 
    simp at h9 ⊢ 
    linarith 
  intro y 
  have h12 : f y = f (f 0) + y := h1 y 
  rw [h8] at h12 
  linarith