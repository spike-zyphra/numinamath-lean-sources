import Mathlib

/- Determine the smallest positive integer $n$ such that $5^n\equiv n^5\pmod 3$. -/
theorem number_theory_12518 :
    IsLeast {n : ℕ | 0 < n ∧ (5 ^ n) % 3 = (n ^ 5) % 3} 4 := by
  refine' ⟨by decide, fun y hy => _⟩
  by_contra! h
  norm_num at hy
  revert hy
  revert y
  decide