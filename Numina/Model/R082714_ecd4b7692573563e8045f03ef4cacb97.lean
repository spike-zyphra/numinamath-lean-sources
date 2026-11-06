import Mathlib

theorem algebra_8169 {f : ℝ → ℝ} (h : ∀ x y, f (x * y) = f x + f y) :
    ∀ x, f x = 0 := by
  have h0 : f 0 = 0 := by 
    specialize h 0 0
    simp at h
    linarith
  intro x
  have hx : f x = 0 := by
    specialize h x 0
    simp [h0] at h
    linarith
  exact hx