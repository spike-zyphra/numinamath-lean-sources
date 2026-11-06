import Mathlib


theorem algebra_271282 {f : ℝ → ℝ} (h : ∀ x y, f (2 * x) + f (2 * y) = f (x + y) * f (x - y))
    (h1 : f Real.pi = 0) (h2 : ∃ x, f x ≠ 0) :
    f = fun x => f (x + 4 * Real.pi) := by

  have h3 : ∀ x, f (x + 2 * Real.pi) = - f x := by
    intro x
    have eq1 := h ((x + 2 * Real.pi) / 2) (x / 2)
    have eq2 : 2 * ((x + 2 * Real.pi) / 2 : ℝ) = x + 2 * Real.pi := by ring
    have eq3 : 2 * ((x / 2 : ℝ)) = x := by ring
    have eq4 : ((x + 2 * Real.pi) / 2 : ℝ) + (x / 2 : ℝ) = x + Real.pi := by ring
    have eq5 : ((x + 2 * Real.pi) / 2 : ℝ) - (x / 2 : ℝ) = Real.pi := by ring
    rw [eq2, eq3, eq4, eq5] at eq1
    rw [h1] at eq1
    linarith

  funext x
  have eq1 : f (x + 4 * Real.pi) = f (x + 2 * Real.pi + 2 * Real.pi) := by ring_nf
  rw [eq1]
  have eq3 : f (x + 2 * Real.pi + 2 * Real.pi) = - f (x + 2 * Real.pi) := by
    have h3' : ∀ y, f (y + 2 * Real.pi) = - f y := by
      intro y
      have eq1 := h3 y
      linarith
    specialize h3' (x + 2 * Real.pi)
    have eq4 : (x + 2 * Real.pi) + 2 * Real.pi = x + 2 * Real.pi + 2 * Real.pi := by ring
    rw [eq4] at h3'
    linarith
  have eq4 : f (x + 2 * Real.pi) = - f x := h3 x
  rw [eq3, eq4]
  all_goals ring_nf