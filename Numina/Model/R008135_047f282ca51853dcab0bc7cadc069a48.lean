import Mathlib

theorem algebra_137426 :
    {f : ℝ → ℝ | ∀ x y, f (x * y) = x * f y + 3 * f x + 3} = {fun x => x / 2 - 3 / 2} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume $f$ satisfies the equation, prove $f(x) = \frac{1}{2} x - \frac{3}{2}$
    intro hf
    have h1 := hf 0 0
    have f0 : f 0 = -3 / 2 := by
      norm_num at h1
      linarith
    have h_eq : ∀ x, f x = x / 2 - 3 / 2 := by
      intro x
      have h2 := hf x 0
      simp [show f 0 = -3 / 2 by linarith [f0]] at h2
      linarith
    funext x
    exact h_eq x
  · -- Show that $f(x) = \frac{1}{2} x - \frac{3}{2}$ satisfies the equation
    intro hf
    intro x y
    simp [hf]
    <;> ring