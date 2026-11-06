import Mathlib

theorem number_theory_12578 : ∑ x in (504 : ℕ).divisors.filter Even, x = 1456 := by
  native_decide