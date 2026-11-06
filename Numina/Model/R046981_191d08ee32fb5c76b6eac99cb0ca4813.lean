import Mathlib

theorem algebra_5658 {P : Polynomial ℝ} (hP : ∀ x : ℝ, P.eval x = P.eval (x + 1)) :
    ∃ c, P = c := by
  refine' ⟨P, rfl⟩