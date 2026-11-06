import Mathlib

/- What is the smallest positive integer $n$ such that $n^{2}$ and $(n+1)^{2}$ both contain the digit 7 but $(n+2)^{2}$ does not?-/
theorem number_theory_611465 :
    IsLeast {n : ℕ | 0 < n ∧ 7 ∈ Nat.digits 10 (n ^ 2) ∧ 7 ∈ Nat.digits 10 ((n + 1) ^ 2) ∧ 7 ∉ Nat.digits 10 ((n + 2) ^ 2)} 27 := by
  -- Break the goal into two parts.
  simp only [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- Show that 27 belongs to the set.
    simp
  . -- Show that 27 is the least such number.
    simp
    intro n hn h₁ h₂ h₃ h₄
    by_contra!
    -- For n < 27, check that it does not satisfy the condition.
    interval_cases n
    <;> simp_all