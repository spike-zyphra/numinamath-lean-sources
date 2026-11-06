import Mathlib

/-"Let $b$ be an integer base. Let $N_1, N_2, N_3$ be natural numbers whose decimal digits are
$d_{1,k_1} \dots d_{1,0}$, $d_{2,k_2} \dots d_{2,0}$, and $d_{3,k_3} \dots d_{3,0}$ respectively.
Assume all digits $d_{i,j}$ satisfy $0 \le d_{i,j} < b$.
Let $val(X, b)$ denote the number obtained by interpreting the decimal representation of $X$ as a base-$b$ number
(for example, if $X=x_m \ldots x_0$ in base 10, then $val(X, b) = \sum_{j=0}^m x_j b^j$).
Let $V = val(N_1, b) - val(N_2, b) - val(N_3, b)$.
Let $R$ be a natural number whose decimal digits $r_p \dots r_0$ are also all less than $b$.
Theorem: For $N_1=513$, $N_2=124$, $N_3=205$, and base $b=7$, the identity $val(N_1, b) - val(N_2, b) - val(N_3, b) = val(R, b)$
holds if $R=151$."
-/

theorem number_theory_634801 (b: ℕ) (h1: b = 7): (5 * b ^ 2 + 1 * b + 3) - (1 * b ^ 2 + 2 * b + 4) - (2 * b ^ 2 + 0 * b + 5)
  = (1 * b ^ 2 + 5 * b + 1) := by

  simp [h1]