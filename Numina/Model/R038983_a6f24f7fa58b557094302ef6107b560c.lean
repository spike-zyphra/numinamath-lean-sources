import Mathlib

theorem algebra_129302 :
    {f : ℝ → ℝ | ∀ x y, f (x + y) = 2 * f x + f y} = {fun x => 0} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, we assume $f$ satisfies the functional equation, and prove $f = 0$.
    intro h
    have h1 : f 0 = 0 := by
      specialize h 0 0
      simp at h
      linarith
    have h2 : ∀ x, f x = 0 := by
      intro x
      have eq1 := h x 0
      simp [h1] at eq1
      linarith
    funext x
    apply h2 x
  · -- Now, we prove the converse: the zero function satisfies the equation.
    intro hf
    rw [hf]
    intro x y
    simp