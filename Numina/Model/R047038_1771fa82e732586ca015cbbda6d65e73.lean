import Mathlib

theorem phifun (p : ℝ → ℝ → ℝ → ℝ) (f g : ℝ → ℝ → ℝ) 
(prop1 : ∀ x y z, p x y z = f (x + y) z)
(prop2 : ∀ x y z, p x y z = g x (y + z)) :
∃ h : ℝ → ℝ, ∀ x y z, p x y z = h (x + y + z) := by 
  use λ w => g 0 w
  intro x y z
  have eq1 : p x y z = f (x + y) z := by
    apply prop1
  have eq2 : f (x + y) z = g 0 ((x + y) + z) := by
    have h1 : ∀ y' z', f y' z' = g 0 (y' + z') := by
      intro y' z'
      have eq1' : p 0 y' z' = f y' z' := by
        specialize prop1 0 y' z'
        simpa using prop1
      have eq2' : p 0 y' z' = g 0 (y' + z') := by
        specialize prop2 0 y' z'
        simpa using prop2
      linarith
    specialize h1 (x + y) z
    simpa using h1
  have eq3 : p x y z = g 0 (x + y + z) := by
    have eq3' : f (x + y) z = g 0 ((x + y) + z) := eq2
    have eq3'' : (x + y) + z = x + y + z := by ring
    rw [eq3''] at eq3'
    linarith [eq1, eq3']
  simpa using eq3