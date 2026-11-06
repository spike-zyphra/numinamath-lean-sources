import Mathlib

theorem algebra_111277 {f : ℝ → ℝ} (h : ∀ x y, f (f (f x)) + f (f y) = f y + x) :
    ∀ x, f x = x := by

  have eq1 : ∀ x, f (f (f x)) = x + (f 0 - f (f 0)) := by
    intro x
    have h1 := h x 0
    simp at h1
    linarith

  have eq2 : ∀ y, f (f y) = f y - (f 0 - f (f 0)) := by
    intro y
    have h2 := h 0 y
    simp at h2
    have h3 := eq1 0
    simp at h3
    linarith

  have h1 : ∀ x, f x = x + 3 * (f 0 - f (f 0)) := by
    intro x
    have eq3 := eq1 x
    have eq4 := eq2 x
    have eq5 : f (f (f x)) = x + (f 0 - f (f 0)) := eq3
    rw [eq2 (f x)] at eq3
    linarith [eq4]

  have c_eq : f 0 - f (f 0) = 0 := by
    have hfx1 : f 0 = (0 : ℝ) + 3 * (f 0 - f (f 0)) := by
      apply h1
    have hfx2 : f (f 0) = f 0 + 3 * (f 0 - f (f 0)) := by
      apply h1
    have hfx3 : f (f (f 0)) = f (f 0) + 3 * (f 0 - f (f 0)) := by
      apply h1
    have eq1_0 : f (f (f 0)) = (0 : ℝ) + (f 0 - f (f 0)) := eq1 0
    linarith [hfx1, hfx2, hfx3, eq1_0]

  have hfx : ∀ x, f x = x := by
    intro x
    specialize h1 x
    rw [c_eq] at h1
    linarith

  exact hfx