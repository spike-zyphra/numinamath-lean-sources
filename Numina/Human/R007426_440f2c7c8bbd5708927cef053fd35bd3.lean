import Mathlib

/- How many positive integers less than $101$ are multiples of either $5$ or $7$, but not both at once? -/
theorem algebra_14137 (S : Finset ℕ) (hs : S = {n ∈ Finset.range 101 | 0 < n ∧ (5 ∣ n ∨ 7 ∣ n) ∧ ¬(5 ∣ n ∧ 7 ∣ n)}) :
  S.card = 30 := by
  -- we can list all possible number satisfy this condition
  have heq : S = {
    5, 10, 15, 20, 25, 30, 40, 45, 50, 55, 60, 65, 75, 80, 85, 90, 95, 100,
    7, 14, 21, 28, 42, 49, 56, 63, 77, 84, 91, 98
  } := by
    rw [hs]
    ext x
    constructor
    .
      intro hx; simp
      push_cast at hx
      fin_cases hx
      any_goals simp
    .
      intro hx
      fin_cases hx
      any_goals simp; decide
  rw [heq]
  -- then count this set, we get 30
  simp
