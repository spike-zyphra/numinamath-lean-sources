import Mathlib

theorem algebra_255775 (φ : ℝ → ℝ → ℝ → ℝ)
    (f g : ℝ → ℝ → ℝ)
    (hfg : ∀ x y z, φ x y z = f (x + y) z ∧ φ x y z = g x (y + z)) :
    ∃ h : ℝ → ℝ, ∀ x y z, φ x y z = h (x + y + z) := by
  have eq1 : ∀ x y z, φ x y z = f (x + y) z := by
    intro x y z
    exact (hfg x y z).1
  have eq2 : ∀ x y z, φ x y z = g x (y + z) := by
    intro x y z
    exact (hfg x y z).2
  have eq3 : ∀ u v, f u v = g 0 (u + v) := by
    intro u v
    have eq3' : φ 0 u v = f (0 + u) v := by
      apply eq1 0 u v
    have eq4' : φ 0 u v = g 0 (u + v) := by
      specialize eq2 0 u v
      simpa using eq2
    rw [show 0 + u = (u : ℝ) by ring] at eq3'
    linarith [eq3', eq4']
  use fun w => g 0 w
  intro x y z
  have eq5 : φ x y z = f (x + y) z := eq1 x y z
  have eq6 : f (x + y) z = g 0 (x + y + z) := by
    have eq7 : f (x + y) z = g 0 ( (x + y) + z ) := by
      simpa using eq3 (x + y) z
    have eq8 : (x + y) + z = x + y + z := by ring
    rw [eq8] at eq7
    linarith
  rw [eq5, eq6]
  all_goals linarith