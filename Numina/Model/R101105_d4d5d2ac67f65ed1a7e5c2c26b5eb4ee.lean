import Mathlib

theorem number_theory_13047 : ¬∃ x y : ℕ, x > 0 ∧ y > 0 ∧ 20 * x ^ 2 + 17 * y ^ 2 = 803 := by 
  intro h
  rcases h with ⟨x, y, hx, hy, heq⟩
  have hx1 : x ≤ 6 := by
    nlinarith [heq]
  have hy1 : y ≤ 6 := by
    nlinarith [heq]
  interval_cases x <;> interval_cases y <;> omega