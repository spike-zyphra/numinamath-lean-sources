import Mathlib

/-- Define matA as
$$
\left(\begin{array}{rrrrr}
1 & 2 & 3 & 5 & 8 \\
0 & 1 & 4 & 6 & 9 \\
0 & 0 & 1 & 7 & 10
\end{array}\right)
$$-/
def matA : Matrix (Fin 3) (Fin 5) ℝ :=
  !![1, 2, 3, 5, 8; 0, 1, 4, 6, 9; 0, 0, 1, 7, 10]

/-- Define matB as
\left(\begin{array}{rrrrr}
1 & 0 & 0  \\
0 & 1 & 0  \\
0 & 0 & 1  \\
0 & 0 & 0  \\
0 & 0 & 0  \\
\end {array} \right)-/
def matB : Matrix (Fin 5) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1, 0; 0, 0, 1; 0, 0, 0; 0, 0, 0]

/-- Given the following matrix:
$$
A=\left(\begin{array}
1 & 2 & 3 & 5 & 8 \\
0 & 1 & 4 & 6 & 9 \\
0 & 0 & 1 & 7 & 10
\end{array}\right)
$$
Determine its rank.-/
theorem linear_algebra_4229 : Matrix.rank matA = 3 := by
-- the rank of matA less than or equal 3
have r1 := Matrix.rank_le_card_height matA
simp at r1
have r2 : matA * matB = !![1, 2, 3; 0, 1, 4; 0, 0, 1] := by
  simp only [matA, matB]; ext i j; simp
have r3 : (matA * matB).det = 1 := by
  rw [r2]; rw [Matrix.det_fin_three]; simp
have r4 : IsUnit (matA * matB) := by
  apply (Matrix.isUnit_iff_isUnit_det (matA * matB)).mpr
  rw [r3]; simp
-- the rank of product of matA and matB is 3
have r5 : Matrix.rank (matA * matB) = 3 := by
  rw [Matrix.rank_of_isUnit]; simp; exact r4
-- the rank of matA greater than 3
have r6 : 3 ≤ Matrix.rank matA := by
  have := Matrix.rank_mul_le_left matA matB
  rw [r5] at this; exact this
linarith
