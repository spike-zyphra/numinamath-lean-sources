import Mathlib

/-Let $X$ be a real number such that $2X$ is an integer and $20 \le X \le 182$. On a long strip of paper,
the numbers $1, 2, 3, \ldots, n$ are written in sequence. The strip is cut into five segments.
The averages of the numbers in these five segments are $345, 19, 1234, X, \text{ and } 9.5$.
The order of these five averages is scrambled. Determine the value of $n$. Show the answer is $1758+2X$.-/

theorem number_theory_40428 (X: ℝ) (n: ℤ) (h4: ∃ m1 m2 m3 m4: ℤ, 0 < m1 ∧ m1 < m2 ∧ m2 < m3 ∧ m3 < m4 ∧ m4 < n ∧
  (1 + m1) / (2: ℝ) = 9.5 ∧ (m1 + 1 + m2) / (2: ℝ) = 19 ∧ (m2 + 1 + m3) / (2: ℝ) = X ∧ (m3 + 1 + m4) / (2: ℝ) = 345 ∧
  (m4 + 1 + n) / (2: ℝ) = 1234): n = 1758 + 2 * X := by

  obtain ⟨m1, m2, m3, m4, hm⟩ := h4
  nlinarith