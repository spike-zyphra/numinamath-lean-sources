import Mathlib

/- When $x$ is divided by each of $4$, $5$, and $6$, remainders of $3$, $4$, and $5$ (respectively) are obtained. What is the smallest possible positive integer value of $x$? -/
theorem number_theory_11006 : IsLeast {x | 0 < x ∧ x % 4 = 3 ∧ x % 5 = 4 ∧ x % 6 = 5} 59 := by
  exact ⟨by decide, fun a ⟨h₀, h₁, h₂, h₃⟩ => by omega⟩