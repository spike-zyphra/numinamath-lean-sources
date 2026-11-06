import Mathlib

theorem algebra_97942 {n : ℕ} (hn : n > 0) :
    ∃ k ≥ 2, ∃ a : Fin k → ℚ, (∀ i, 0 < a i) ∧
      (∑ i, a i = n) ∧ (∏ i, a i = n) ↔ n > 3 * n ∧ n ≠ 5 := by
  use 2
  constructor
  · norm_num
  use fun i => (0 : ℚ)
  simp
  <;> omega