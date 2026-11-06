import Mathlib

/- All of the even numbers from 2 to 98 inclusive, except those ending in 0, are multiplied together. What is the rightmost digit (the units digit) of the product? -/
theorem number_theory_19586 : (∏ i ∈ (Finset.Icc 2 98).filter (fun x => Even x ∧ ¬x % 10 = 0), i) % 10 = 6 := by
  exact rfl