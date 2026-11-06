import Mathlib

/- What is the sum of all positive integer solutions less than or equal to $20$ to the congruence $13(3x-2)\equiv 26\pmod 8$? -/
theorem number_theory_15408 :
    ∑ x in (Finset.Icc 1 20).filter (fun x => 13 * (3 * x - 2) ≡ 26 [ZMOD 8]), x = 36 := by
  decide