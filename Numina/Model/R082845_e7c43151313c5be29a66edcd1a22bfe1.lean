import Mathlib

theorem algebra_264756 {f : ℝ → ℝ} (h : ∀ x, f (2 - x) = 2 - f x) :
    ∃ n, ∃ x y : Fin n → ℝ, (∀ i, x i ≠ 1) ∧ (∀ i, f (x i) = y i) ∧
    (∀ i, x i / (x i - 1) = y i) ∧ (∑ i, (x i + y i)) = 2 * n := by
  use 0
  use ![], ![]
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp
  · simp