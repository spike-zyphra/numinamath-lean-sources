import Mathlib

/-- Tom's age is $T$ years, which is also the sum of the ages of his three children. His age $N$ years ago was twice the
sum of their ages then. What is $T/N$?
$\textbf{(A) } 2 \qquad\textbf{(B) } 3 \qquad\textbf{(C) } 4 \qquad\textbf{(D) } 5 \qquad\textbf{(E) } 6$ -/
theorem Algebra_1186 (T C N : ℤ) (hN : N ≠ 0) (h1 : T = C) (h2 : T - N = 2*(C - 3*N)) : T/N = 5 := by
  -- To show that $T/N = 5$, it is enough to show that $T = 5N$.
  suffices T = 5*N from by simp [this, hN]

  -- Simplify the second equation.
  rw [←h1, mul_sub, ←mul_assoc, ←neg_add_eq_sub (2*3*N), add_comm, sub_eq_iff_eq_add] at h2
  nth_rw 2 [←one_mul N] at h2
  rw [add_assoc, ←neg_mul, ←right_distrib, add_comm, ←sub_eq_iff_eq_add] at h2
  nth_rewrite 1 [←one_mul T] at h2
  rw [←sub_mul] at h2
  simp at h2
  exact h2