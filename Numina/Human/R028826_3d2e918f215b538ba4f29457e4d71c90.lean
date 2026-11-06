import Mathlib
/- Order these four numbers from least to greatest: $5^{56}, 10^{51}, 17^{35}, 31^{28}$. -/
theorem number_theory_610845 : 5 ^ 56 < 31 ^ 28 ∧ 31 ^ 28 < 17 ^ 35 ∧ 17 ^ 35 < 10 ^ 51 := by
  -- use simp to finish the proof
  simp
