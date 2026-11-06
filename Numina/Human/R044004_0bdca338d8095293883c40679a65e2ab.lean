import Mathlib

/- Prove that $\sqrt 3$ is irrational. -/
theorem number_theory_36178 : Irrational (Real.sqrt 3) := by
  simpa using Nat.Prime.irrational_sqrt (by norm_num)