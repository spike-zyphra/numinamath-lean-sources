import Mathlib

/- What is the least positive integer $n$ such that $n^2 - n$ is divisible by some but not all integer values of $k$ when $1\leq k \leq n$? -/
theorem number_theory_15414 :
    IsLeast {n : ℕ | 0 < n ∧ ∃ k ∈ Finset.Icc 1 n, (n ^ 2 - n) % k ≠ 0} 5 := by 
  refine' ⟨by decide, fun n ⟨h₀, h₁⟩ => _⟩
  refine' le_of_not_lt fun hn => _
  interval_cases n <;> simp_all (config := {decide := true})