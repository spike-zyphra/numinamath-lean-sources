import Mathlib

theorem algebra_2602 {a : ℤ} (ha : 5 - 2 * a ≠ 0) (h : ∃ x, x < 0 ∧ (5 - 2 * a) * x = -2) :
    a ≤ 2 := by
  rcases h with ⟨x, hx1, hx2⟩
  have h1 : (5 - 2 * a) > 0 := by
    nlinarith
  omega