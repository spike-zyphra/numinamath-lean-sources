import Mathlib

/-Let $M$ be an integer greater than 1. Let $N$ be the number of digits of $M^{100}$ when written in base 10.
For $M=5$, determine an integer $k$ such that $k \leq N \leq k+4$. Show that $k=66$ satisfies this condition.-/

theorem number_theory_636444 (M k: ℕ) (h1: M = 5) (h2: k = 66):
  10 ^ (k - 1) ≤ M ^ 100 ∧ M ^ 100 ≤ 10 ^ (k + 4) := by

    simp [h1, h2]