import Mathlib

theorem algebra_165316 (a b c : ℝ) (h : ∃ d, b = a + d ∧ c = b + d) :
    ∃ d, (a^2 + a * b + b^2) + d = a^2 + a * c + c^2 ∧
    (a^2 + a * c + c^2) + d = b^2 + b * c + c^2 := by
  rcases h with ⟨d, h1, h2⟩
  use (a^2 + a * c + c^2) - (a^2 + a * b + b^2)
  constructor
  · -- Show (a^2 + a * b + b^2) + d = a^2 + a * c + c^2
    simp [h1, h2]
    <;> ring
  · -- Show (a^2 + a * c + c^2) + d = b^2 + b * c + c^2
    simp [h1, h2]
    <;> ring
    <;> simp [h1, h2]
    <;> ring