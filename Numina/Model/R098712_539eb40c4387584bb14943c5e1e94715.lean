import Mathlib

theorem algebra_319846 {f g : ℝ → ℝ} (hf : f = fun x => x^2 - 2 * x - 3) :
    ∀ y, ∃ x, x = y^2 - 4 * y + 3 ∨ x = -y^2 - 4 * y + 3 := by
  intro y
  refine ⟨y^2 - 4 * y + 3, Or.inl rfl⟩