import Mathlib

/- The expressions $A = 1 \times 2 + 3 \times 4 + 5 \times 6+ \cdots + 37 \times 38 + 39$ and $B = 1 + 2 \times 3 + 4 \times 5 + \cdots + 36 \times 37 + 38 \times 39$ are obtained by writing multiplication and addition operators in an alternating pattern between successive integers.  Find the positive difference between integers $A$ and $B$.-/
theorem algebra_96146 {A B : ℤ} (hA : A = (∑ i ∈ Finset.range 19, (2 * i + 1) * (2 * i + 2)) + 39) (hB : B = 1 + ∑ i ∈ Finset.range 19, (2 * i + 2) * (2 * i + 3)) : |A - B| = 722 := by 
  -- Use Lean's ring tactic to do the hard calculations automatically, and then simplify. 
  rw [hA, hB]
  ring
  simp