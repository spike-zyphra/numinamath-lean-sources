import Mathlib

/- The expressions $A=1\times2+3\times4+5\times6+\cdots+37\times38+39$ and $B=1+2\times3+4\times5+\cdots+36\times37+38\times39$ are obtained by writing multiplication and addition operators in an alternating pattern between successive integers. Find the positive difference between integers $A$ and $B$. -/
theorem algebra_85760 {A B : ℤ}
    (hA : A = ∑ i ∈ Finset.range 19, (2 * i + 1) * (2 * i + 2) + 39)
    (hB : B = 1 + ∑ i ∈ Finset.range 19, (2 * i + 2) * (2 * i + 3)) :
    |A - B| = 722 := by 
  rw [hA, hB]
  decide