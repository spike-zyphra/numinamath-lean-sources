import Mathlib
theorem geometry_241349 : ∀(a:ℕ),a≥5 → ∃(b:ℕ) (c:ℕ),c≥b∧b≥a → a^2=b^2+c^2 ∨ b^2=a^2+c^2 ∨ c^2=a^2+b^2 := by
  intro a ha
  use 0
  use 0
  intro h
  omega