import Mathlib

/-Let $M$ be a natural number. Let $a$ and $d$ be natural numbers.
Suppose that $a < 10$, $a + 99d = 100$, and $a + 3099d = M$. Show that $d=1$.-/

theorem number_theory_636579
  (a d: ℕ) (ha: a < 10) (h: a + 99 * d = 100): d = 1 := by

  omega