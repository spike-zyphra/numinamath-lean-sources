import Mathlib

open Matrix

/- 12. (SWE 6) Consider the two square matrices

$$

A=\left[\begin{array}{rrrrr}
1 & 1 & 1 & 1 & 1 \\
1 & 1 & 1 & -1 & -1 \\
1 & -1 & -1 & 1 & 1 \\
1 & -1 & -1 & -1 & 1 \\
1 & 1 & -1 & 1 & -1
\end{array}\right] \quad \text { and } \quad B=\left[\begin{array}{rrrrr}
1 & 1 & 1 & 1 & 1 \\
1 & 1 & 1 & -1 & -1 \\
1 & 1 & -1 & 1 & -1 \\
1 & -1 & -1 & 1 & 1 \\
1 & -1 & 1 & -1 & 1
\end{array}\right]

$$

with entries 1 and -1 . The following operations will be called elementary.
(1) Changing signs of all numbers in one row;
(2) Changing signs of all numbers in one column:
(3) Interchanging two rows (two rows exchange their positions);
(4) Interchanging two columns.

Prove that the matrix $B$ cannot be obtained from the matrix $A$ using these operations. -/
theorem algebra_274341 :
  let A := !![1, 1, 1, 1, 1; 1, 1, 1, -1, -1; 1, -1, -1, 1, 1; 1, -1, -1, -1, 1; 1, 1, -1, 1, -1];
  let B := !![1, 1, 1, 1, 1; 1, 1, 1, -1, -1; 1, 1, -1, 1, -1; 1, -1, -1, 1, 1; 1, -1, 1, -1, 1];
    ¬∃ p q : Equiv.Perm (Fin 5), B = A.submatrix p q := by
  intro A B ⟨p, q, h⟩
  -- suppose permutations p and q exist
  -- then the absolute values of the determinants of A and B are equal
  -- but det A = 16 while det B = 0
  absurd calc
    0 = |B.det| := by native_decide
    _ = |A.det| := by rw [h]; apply Matrix.abs_det_submatrix_equiv_equiv
    _ = 16 := by native_decide
  trivial