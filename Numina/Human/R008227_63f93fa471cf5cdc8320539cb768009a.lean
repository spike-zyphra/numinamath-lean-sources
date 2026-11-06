import Mathlib

/- What is the smallest positive integer $N$ such that the value $7 + (30 \times N)$ is not a prime number? -/
theorem number_theory_23136 :
    IsLeast {N : ℕ | 0 < N ∧ ¬Nat.Prime (7 + 30 * N)} 6 := by 
  refine' ⟨by norm_num, fun a h ↦ _⟩
  cases' h with h₁ h₂
  contrapose! h₂
  interval_cases a <;> decide