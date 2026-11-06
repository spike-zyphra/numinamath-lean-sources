import Mathlib

/- Define $x\otimes y=x^3-y$. What is $h\otimes (h\otimes h)$?
$\textbf{(A)}\ -h\qquad\textbf{(B)}\ 0\qquad\textbf{(C)}\ h\qquad\textbf{(D)}\ 2h\qquad\textbf{(E)}\ h^3$ -/

def f (x : ℝ) (y : ℝ)  := x^3 - y
notation x "⊗" y => f x y

theorem Algebra_1165 (h : ℝ) : (h ⊗ (h ⊗ h)) = h := 
by 
  dsimp [f]
  ring