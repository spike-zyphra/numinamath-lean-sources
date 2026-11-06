import Mathlib

/- What is the greatest integer less than or equal to\[\frac{3^{100}+2^{100}}{3^{96}+2^{96}}?\]
$\textbf{(A) }80\qquad \textbf{(B) }81 \qquad \textbf{(C) }96 \qquad \textbf{(D) }97 \qquad \textbf{(E) }625\qquad$
 -/
theorem number_theory_14415 : ⌊(3^100 + 2^100 : ℝ) / (3^96 + 2^96)⌋ = 80 := by
  norm_num [Int.floor_eq_iff]