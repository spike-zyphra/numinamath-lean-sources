import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin

/-- nth triangular number. -/
def t (n : ℕ) : ℚ := n * (n + 1) / 2

/-- Let $t_n = \frac{n(n+1)}{2}$ be the $n$th triangular number. Find
\[\frac{1}{t_1} + \frac{1}{t_2} + \frac{1}{t_3} + ... + \frac{1}{t_{2002}}\]
$\text{(A) }\frac {4003}{2003} \qquad \text{(B) }\frac {2001}{1001} \qquad
\text{(C) }\frac {4004}{2003} \qquad \text{(D) }\frac {4001}{2001} \qquad
\text{(E) }2$ -/
theorem number_theory_1131 : ∑ i ∈ Finset.range 2002, 1 / (t (i + 1)) = 4004/2003 := by
  -- As we know the triangular numbers, this just amounts to a finite calculation.
  native_decide