import Mathlib

/- What is the smallest positive integer $n$ for which $n^2$ is divisible by 18 and $n^3$ is divisible by 640? -/
theorem number_theory_15084 :
    IsLeast {n : ℕ | 0 < n ∧ 18 ∣ n^2 ∧ 640 ∣ n^3} 120 := by
  refine' ⟨by decide, fun n h ↦ _⟩
  refine' le_of_not_lt fun h₁ ↦ _
  interval_cases n <;> norm_num at h