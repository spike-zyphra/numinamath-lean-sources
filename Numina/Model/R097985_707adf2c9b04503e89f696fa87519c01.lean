import Mathlib

open Real

theorem algebra_94617 (a : ℕ → ℝ) (ha : a 0 = 1)
    (h : ∀ n, a (n + 1) = a n + 1 / 4 * sqrt 2 + 1 / 4 + 1 / 16 * sqrt 2 + 1 / 16 +
      1 / 64 * sqrt 2 + 1 / 64) :
    ∃ L, L = (4 + sqrt 2) / 3 := by
  refine ⟨(4 + sqrt 2) / 3, rfl⟩