import Mathlib

theorem number_theory_137576 (q : ℕ → ℕ) (hq : ∀ n, q n < 2 * n)
    (h : ∀ n, q (n + 1) > q n) :
    ∀ m, ∃ a b, a ∈ Set.range q ∧ b ∈ Set.range q ∧ m = a - b ∨ m = a := by 
  intro m 
  refine' ⟨m, 0, _⟩
  simp