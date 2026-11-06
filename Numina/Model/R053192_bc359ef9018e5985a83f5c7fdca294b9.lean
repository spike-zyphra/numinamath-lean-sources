import Mathlib

theorem number_theory_104670 (x : ℤ) : ∃ n, (1/5)*x^5+(1/3)*x^3+(7/15)*x=n := by
  refine ⟨(1/5) * x^5 + (1/3) * x^3 + (7/15) * x, rfl⟩