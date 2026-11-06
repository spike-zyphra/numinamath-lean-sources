import Mathlib

open Matrix

/-
Find the matrix \( C \) such that
\[
C \equiv \left(\begin{array}{ll}
2 & 1 \\
4 & 3
\end{array}\right) \left(\begin{array}{ll}
4 & 0 \\
2 & 1
\end{array}\right) \mod 5
\]
and all entries of \( C \) are nonnegative integers less than 5.
-/
theorem number_theory_4730 : ∀ (i j : Fin 2), !![0,1;2,3] i j % 5 = ((!![2,1;4,3].mulᵣ !![4,0;2,1]) i j ) % 5 := by
  -- To find the matrix \( C \), we first need to perform the matrix multiplication of the two given matrices:
  -- \[
  -- \left(\begin{array}{ll}
  -- 2 & 1 \\
  -- 4 & 3
  -- \end{array}\right) \left(\begin{array}{ll}
  -- 4 & 0 \\
  -- 2 & 1
  -- \end{array}\right)
  -- \]
  -- \[
  -- C = \left(\begin{array}{ll}
  -- 10 & 1 \\
  -- 22 & 3
  -- \end{array}\right)
  -- \]
  have : !![10,1;22,3] = !![2,1;4,3].mulᵣ !![4,0;2,1] := by aesop
  rw [←this]
  intro i j
  -- Then, for each entry, we check to check its modulo 5.
  fin_cases i
  · fin_cases j <;> simp_all
  · fin_cases j <;> simp_all
