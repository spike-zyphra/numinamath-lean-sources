import Mathlib

theorem algebra_129328 {n : ℕ} (hn : n > 0) (h : ∃ x, x > 0 ∧ (1000 + 1 / 10 * x) = 2000 + 1 / 10 * (x - 1000) ∧
    (2000 + 1 / 10 * (x - 1000)) = 3000 + 1 / 10 * (x - 2000)) :
    n = 9 := by
  rcases h with ⟨x, hx_pos, h1, h2⟩
  omega