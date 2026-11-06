import Mathlib

/- Let $K$ be an integer such that $K \ge 37$.
Theorem: There exist rational numbers $x, y$ such that $x > 0, y > 0$, the denominator of $x$ (in reduced form) is less than or equal to $K$, the denominator of $y$ (in reduced form) is less than or equal to $K$, and $x + y = 86/111$. -/
theorem number_theory_635053 (K : ℕ) (hK : 37 ≤ K) :
    ∃ x y : ℚ, x > 0 ∧ y > 0 ∧ x.den ≤ K ∧ y.den ≤ K ∧ x + y = 86 / 111 := by
  -- We show that x = 2 / 3 and y = 4 / 37 satisfy the conditions.
  use 2 / 3, 4 / 37
  norm_num
  -- 3 ≤ 37 ≤ K
  exact ⟨(show 3 ≤ 37 by simp).trans hK, hK⟩