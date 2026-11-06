import Mathlib

/- \begin{align*}
2a + 3b + 5c + 7d &= 34 \\
3(d+c) &= b \\
3b + c &= a \\
c - 1 &= d \\
\end{align*} Given the above system of equations, find $a \cdot b \cdot c \cdot d$. -/
theorem algebra_11265 {a b c d : ℝ} (h₀ : 2*a+3*b+5*c+7*d=34) (h₁ : 3*(d+c)=b)
    (h₂ : 3*b+c=a) (h₃ : c-1=d) : a*b*c*d=0 := by
  have : c = 1 := by linarith
  have : d = 0 := by linarith
  have : b = 3 := by linarith
  have : a = 10 := by linarith
  subst_vars
  linarith