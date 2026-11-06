import Mathlib

theorem other_140706 (h : ∃ x, x > 0 ∧ (x / 20) * 600 = 2 * x) :
    x = 2 := by
  rcases h with ⟨x, hx_pos, h_eq⟩
  -- Solve the equation (x / 20) * 600 = 2 * x
  omega