import Mathlib

/- Find the smallest positive integer whose cube ends in $888$.
 -/
theorem number_theory_13474 :
    IsLeast {n : ℕ | 0 < n ∧ (n ^ 3) % 1000 = 888} 192 := by
  refine' ⟨by decide, _⟩
  rintro n ⟨h₀, h₁⟩
  norm_num at h₁
  contrapose! h₁
  interval_cases n <;> omega