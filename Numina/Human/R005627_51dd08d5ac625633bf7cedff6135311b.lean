import Mathlib

/- Find the remainder when $1^{2}+3^{2}+5^{2}+\cdots+99^{2}$ is divided by 1000 . -/
theorem number_theory_609165 : (∑ k in (Finset.range 50), (2 * k + 1) ^ 2) % 1000 = 650 := by
  norm_num