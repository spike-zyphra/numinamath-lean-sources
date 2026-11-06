import Mathlib

theorem number_theory_70193 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (h1 : ∃ m, a m = (a 0)^2) (h2 : ∃ n, a n = (a 1)^2) (h3 : ∃ p, a p = (a 2)^2) :
    ∀ k, ∃ j, a k = j := by
  intro k
  refine ⟨a k, rfl⟩