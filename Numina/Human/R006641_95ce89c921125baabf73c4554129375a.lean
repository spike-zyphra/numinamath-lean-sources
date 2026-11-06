import Mathlib

/-Let $N$ and $k$ be natural numbers. Show that $N - (7 \times 11 \times 13) \times k$ is equal to $N - 1001k$.-/

theorem number_theory_639542 (N k: ℤ): N - (7 * 11 * 13) * k = N - 1001 * k := by
  ring