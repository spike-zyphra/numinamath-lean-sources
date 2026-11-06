import Mathlib

/- When $1 + 7 + 7^2 + \cdots + 7^{2004}$ is divided by $1000$, a remainder of $N$ is obtained. Determine the value of $N$.
 -/
theorem number_theory_14633 : (∑ i ∈ Finset.range 2005, 7^i) % 1000 = 801 := by
  rw [Finset.sum_range_succ]
  native_decide
