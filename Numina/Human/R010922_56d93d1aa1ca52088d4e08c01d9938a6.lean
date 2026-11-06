import Mathlib

/- What is the sum of the units digits of all the multiples of $3$ between $0$ and $50$? -/
theorem number_theory_23510 : ∑ n in (Finset.Icc 0 50).filter (fun x => 3 ∣ x), n % 10 = 78 := by
  rfl