import Mathlib

/-Let $m$ be an integer greater than or equal to 2.
Let $N$ be a six-digit number of the form $\overline{d97861}$ (where $d$ denotes the first digit, so $d \in \{1, \dots, 9\}$).
Suppose $N$ is a multiple of $m$, and $d$ is uniquely determined
(i.e., there is only one integer $d$ in the range $\{1, \dots, 9\}$ satisfying the condition).
Determine the value of $d$ and the quotient $N/m$. Show that for $m=33$, the answer is $d=5$ and $N/m = 18117$.-/

theorem number_theory_637404 (d N: ℕ) (hd: 1 ≤ d ∧ d ≤ 9)
  (h1: N = d * 10^5 + 97861) (h2: 33 ∣ N): d = 5 ∧ N / 33 = 18117 := by

  omega
