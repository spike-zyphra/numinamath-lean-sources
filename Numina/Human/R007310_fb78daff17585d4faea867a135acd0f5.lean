import Mathlib

/- What is the smallest positive integer $n$ for which $9n-2$ and $7n + 3$ share a common factor greater than $1$? -/
theorem number_theory_15030 :
    IsLeast {n : ℕ | 0 < n ∧ Nat.gcd (9 * n - 2) (7 * n + 3) > 1} 23 := by
  refine' ⟨by decide, fun n hn ↦ _⟩
  refine' Nat.le_of_not_lt fun h ↦ _
  interval_cases n <;> simp_all