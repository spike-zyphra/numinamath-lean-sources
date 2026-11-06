import Mathlib

/-- Let $\( a_{1}, \ldots, a_{n} \)$ be pairwise distinct numbers. Prove that the system of linear equations

$$
\left\{\begin{array}{l}
x_{1}+\ldots+x_{n}=0 \\
a_{1} x_{1}+\ldots+a_{n} x_{n}=0 \\
7 a_{1}^{2} x_{1}+\ldots+a_{n}^{2} x_{n}=0 \\
\ldots \ldots \ldots \ldots \ldots \ldots \ldots \ldots \ldots \\
a_{1}^{n-1} x_{1}+\ldots+a_{n}^{n-1} x_{n}=0
\end{array}\right.
$$

has only the trivial solution.-/
theorem linear_algebra_4230 (n : ℕ)(a x : Fin n → ℝ)(ha : ∀ i j, a i = a j → i = j):
(heq : Matrix.mulVec (Matrix.vandermonde a) x = 0) → x = 0 := by
contrapose!; intro hx
-- the determinant of vandermonde not equal zero.
have r1: (Matrix.vandermonde a).det ≠ 0 := by
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  rw [Function.Injective]; exact ha
intro hcon
-- the determinant of vandermonde equal zero.
have r2 : (Matrix.vandermonde a).det = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp; use x
-- there is contridiction 
contradiction