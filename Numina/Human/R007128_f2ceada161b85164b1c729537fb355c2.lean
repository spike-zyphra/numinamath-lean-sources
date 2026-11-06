import Mathlib

/- Some of the values produced by two functions, $f(x)$ and $g(x)$, are shown below. Find $f(g(3))$
\begin{tabular}{c||c|c|c|c|c}
$x$ & 1 & 3 & 5 & 7 & 9 \\ \hline\hline
$f(x)$ & 3 & 7 & 9 & 13 & 17 \\ \hline
$g(x)$ & 54 & 9 & 25 & 19 & 44 
\end{tabular}

$\textbf{(A) }3\qquad\textbf{(B) }7\qquad\textbf{(C) }8\qquad\textbf{(D) }13\qquad\textbf{(E) }17$ -/
theorem algebra_35871 {f g : ℝ → ℝ}
    (hf : f 1 = 3 ∧ f 3 = 7 ∧ f 5 = 9 ∧ f 7 = 13 ∧ f 9 = 17)
    (hg : g 1 = 54 ∧ g 3 = 9 ∧ g 5 = 25 ∧ g 7 = 19 ∧ g 9 = 44) :
    f (g 3) = 17 := by 
  aesop