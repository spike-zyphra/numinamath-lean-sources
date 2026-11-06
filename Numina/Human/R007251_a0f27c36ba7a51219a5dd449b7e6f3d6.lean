import Mathlib

/- If $(x + 1) + (x + 2) + ... + (x + 20) = 174 + 176 + 178 + ... + 192$, then what is the value of $x$?

$\mathrm{(A) \ } 80 \qquad \mathrm{(B) \ } 81 \qquad \mathrm {(C) \ } 82 \qquad \mathrm{(D) \ } 83 \qquad \mathrm{(E) \ } 84$
 -/
theorem algebra_67497 (x : ℤ) (h : ∑ i ∈ Finset.range 20, (x + i + 1) = ∑ i ∈ Finset.range 10, (174 + 2 * i)) :
    x = 81 := by
  simp_all [Finset.sum_range_succ]
  linarith