import Mathlib

/-Let $N_0$ be the current year. A student's age in the year $N_0$
is equal to the sum of the digits of their birth year $y$.
It is given that the birth year $y$ is a positive integer strictly less than $N_0$.
If $N_0=1977$, show that the student's age is 21.-/

theorem number_theory_639678 (N_0 y: ℕ) (h1: N_0 = 1977) (h2: y < N_0)
  (h3: ∃ a b c d, a < 2 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧ y = 1000 * a + 100 * b + 10 * c + d ∧ N_0 - y = a + b + c + d):
    N_0 - y = 21 := by

    omega