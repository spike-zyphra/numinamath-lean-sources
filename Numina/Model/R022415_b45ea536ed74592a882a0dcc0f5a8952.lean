import Mathlib

theorem algebra_127689 (f : ℝ → ℝ) (h : ∀ x y, f (f (x + 1) + y - 1) = f x + y) :
    ∀ x, f x = x := by
  have eq1 : ∀ x, f (x + 1) = f x + 1 - f 0 := by
    intro x
    have h1 := h x (1 - f (x + 1))
    simp at h1
    linarith
  have h2 : f 1 = 1 := by
    specialize eq1 0
    norm_num at eq1 ⊢
    linarith
  have eq2 : ∀ y, f y = f 0 + y := by
    intro y
    have h3 := h 0 y
    simp [h2] at h3
    linarith
  have eq3 : ∀ x, f x = 2 * f 0 + x := by
    intro x
    have eq4 : f (x + 1) = f x + 1 - f 0 := eq1 x
    have eq5 : f (x + 1) = f 0 + (x + 1 : ℝ) := by
      apply eq2
    linarith
  have h4 : f 0 = 0 := by
    specialize eq3 0
    norm_num at eq3
    linarith
  intro x
  specialize eq3 x
  rw [h4] at eq3
  linarith