import Mathlib

theorem number_theory_234741 (n : ℕ) (hn : 1 < n) :
    ∃ k : ℤ, (2^n + 1) / n^2 = k ↔ n = 3 := by
  by_cases h : n = 3
  · -- If n = 3, then k = 1.
    use 1
    simp [h]
    <;> omega
  · -- If n ≠ 3, then k is defined to make the equivalence false
    use (2^n + 1 : ℤ) / (n ^ 2 : ℤ) + 1
    simp [h]
    all_goals
      omega