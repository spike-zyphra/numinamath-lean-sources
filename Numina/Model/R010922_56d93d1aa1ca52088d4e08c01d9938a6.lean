import Mathlib

theorem number_theory_23510 : ∑ n in (Finset.Icc 0 50).filter (fun x => 3 ∣ x), n % 10 = 78 := by
  rfl