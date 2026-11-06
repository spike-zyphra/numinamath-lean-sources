import Mathlib

theorem number_theory_243319 :
    ∃ a b : ℕ, IsSquare (a^2 + 2 * b^2) ∧ IsSquare (b^2 + 2 * a) := by 
  use 0, 0
  constructor
  · -- Show $0^2 + 2 \cdot 0^2$ is a square
    exact ⟨0, by norm_num⟩
  · -- Show $0^2 + 2 \cdot 0$ is a square
    exact ⟨0, by norm_num⟩