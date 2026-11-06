import Mathlib

open Real Set
open scoped Real

theorem algebra_179072 {α : ℝ} (h : 2 / tan α ^ 2 + 7 / tan α + 3 = 0) :
    α ∈ Ioo (3 * π / 2) (7 * π / 4) → cos (2 * α) = -3 / 5 ∧
    α ∈ Ioo (7 * π / 4) (2 * π) → cos (2 * α) = 4 / 5 := by 
  intro h1 h2
  rcases h1 with ⟨h11, h12⟩
  rcases h2 with ⟨h21, h22⟩
  rcases h22 with ⟨h221, h222⟩
  -- We have α < 7π/4 from h1 and 7π/4 < α from h221, which is a contradiction.
  have h3 : False := by
    linarith [h12, h221]
  -- Since we derived False, we can prove the goal.
  exfalso
  exact h3