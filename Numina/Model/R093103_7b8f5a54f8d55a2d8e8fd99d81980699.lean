import Mathlib

theorem inequalities_230274 (a : Fin 20 → ℝ) (ha : ∀ i j k, a i ≠ a j ∧ a i ≠ a k ∧ a j ≠ a k)
    (h : ∀ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k → a i < a j + a k) :
    ∀ i, a i > 18 := by
  have h1 := ha 0 0 0
  simp at h1
  all_goals linarith