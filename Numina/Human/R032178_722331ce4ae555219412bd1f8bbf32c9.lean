import Mathlib

/- Define $x\otimes y=x^3-y$. What is $h\otimes (h\otimes h)$?
$\textbf{(A)}\ -h\qquad\textbf{(B)}\ 0\qquad\textbf{(C)}\ h\qquad\textbf{(D)}\ 2h\qquad\textbf{(E)}\ h^3$ -/

def f (x : ℝ) (y : ℝ)  := x^3 - y
notation x "⊗" y => f x y

theorem Algebra_1165 (h : ℝ) : (h ⊗ (h ⊗ h)) = h := 
by
--By the definition of $\otimes$, we have $h\otimes h=h^{3}-h$.
have H : (h ⊗ h) = h^3 - h := by rw [f]
--Then, $h\otimes (h\otimes h)=h\otimes (h^{3}-h)=h^{3}-(h^{3}-h)=\boxed{\textbf{(C) }h}.$
rw [H, f]
exact sub_sub_self (h^3) h