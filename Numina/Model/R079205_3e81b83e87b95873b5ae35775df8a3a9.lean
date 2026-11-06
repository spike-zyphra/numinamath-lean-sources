import Mathlib

theorem number_theory_321669 (a : ℕ) (ha : 2 ≤ a) :
    ∃ b ∈ Finset.Icc 1 a, ∃ x, (a ^ x) = (a + 1) * x + b := by
  use 1
  constructor
  · -- Show that 1 is in the interval [1, a]
    simp [Finset.mem_Icc]
    all_goals omega -- this tactic handles rewriting the goal assuming ha that a ≥ 2
  · -- Show there exists some x
    use 0
    simp -- This will rewrite the expressions so that trivial equality holds