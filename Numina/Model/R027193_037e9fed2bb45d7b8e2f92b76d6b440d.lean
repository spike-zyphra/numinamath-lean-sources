import Mathlib

theorem algebra_1414 {f g : ℝ → ℝ} (h₁ : ∀ x, f (g (f x)) = g x)
(h₂ : ∀ x, g (f (f x)) = f x) :
∀ x, f x = g x := by
  intro x
  have h3 : ∀ y, g (f y) = f (f y) := by
    intro y
    have eq1 : g (f (f y)) = f y := h₂ y
    have eq2 : f (g (f (f y))) = f (f y) := by
      rw [show g (f (f y)) = f y by linarith [eq1]]
    have eq3 : f (g (f (f y))) = g (f y) := by
      specialize h₁ (f y)
      simpa using h₁
    linarith
  have h4 : ∀ y, f (f (f y)) = f y := by
    intro y
    have eq1 : g (f (f y)) = f y := h₂ y
    have eq2 : g (f (f y)) = f (f (f y)) := by
      have h3' : ∀ a, g (f a) = f (f a) := h3
      specialize h3' (f y)
      simpa using h3'
    linarith
  have h5 : f (f (f x)) = f x := h4 x
  have eq1 : f (g (f x)) = g x := h₁ x
  have eq2 : g (f x) = f (f x) := h3 x
  have eq3 : f (g (f x)) = f (f (f x)) := by
    rw [eq2]
  have eq4 : f (g (f x)) = f x := by
    rw [eq3]
    linarith [h4 x]
  linarith [eq1, eq4]