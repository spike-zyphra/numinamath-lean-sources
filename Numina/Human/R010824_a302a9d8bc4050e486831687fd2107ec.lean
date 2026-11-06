import Mathlib

/- What is the least positive integer value of $x$ such that $(2x)^2 + 2\cdot 37\cdot 2x + 37^2$ is a multiple of 47? -/
theorem algebra_11293 :
    IsLeast {x : ℕ | 0 < x ∧ 47 ∣ (2 * x) ^ 2 + 2 * 37 * 2 * x + 37 ^ 2} 5 := by
  refine' ⟨by decide, fun x ⟨h0, h⟩ => _⟩
  norm_num at h
  contrapose! h
  interval_cases x <;> norm_num