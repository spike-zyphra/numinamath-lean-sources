import Mathlib

theorem number_theory_305124 : IsSquare ((1997 * 1998 * 1999 * 2000 + 1)) ∧
    ∃ n, n^2 = 1997 * 1998 * 1999 * 2000 + 1 := by
  constructor
  · -- Show that 1997 * 1998 * 1999 * 2000 + 1 is a perfect square
    native_decide
  · -- Show that there exists an integer n such that n^2 = 1997 * 1998 * 1999 * 2000 + 1
    use 3994001
    all_goals
    native_decide