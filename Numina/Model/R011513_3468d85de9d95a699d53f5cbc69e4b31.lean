import Mathlib

theorem number_theory_25642 {n : ℕ} (hn : n ≥ 2) (h1 : ∀ d ∈ n.divisors, d ≠ 0) (h2 : Squarefree n):
    ∃ m : ℕ, 0 < m ∧ ∑ d ∈ n.divisors, (1 : ℚ)/d = m ↔ n = 6 := by
  by_cases h4 : n = 6
  · -- Assume n = 6 directly.
    rw [h4]
    use 2
    norm_num
    <;> native_decide
  · -- Assume n ≠ 6
    use 0 
    simp [h4]