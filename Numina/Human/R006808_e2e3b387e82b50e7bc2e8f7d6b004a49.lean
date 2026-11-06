import Mathlib


/- Let $N$ and $K$ be positive integers such that $K \le N$. Let $T_m = m(m+1)/2$ denote
the $m$-th triangular number. A triangular number array is arranged such that the $K$-th number
from the left in the $N$-th row (which is assumed to have at least $K$ elements) corresponds to
the triangular number $T_{N^2+K-1}$. Determine the value of the $K$-th number from the left in
the $N$-th row. Show that the answer is $\frac{(N^2+K-1)(N^2+K)}{2}$. -/


-- define the triangular number function
noncomputable def T (m : ℕ) : ℕ := m * (m + 1) / 2

set_option linter.unusedVariables false

theorem number_theory_641351 (N K : ℕ) (hK : K > 0) (hN : N > 0) (hNK : K ≤ N) :
    T (N ^ 2 + K - 1) = (N ^ 2 + K - 1) * (N ^ 2 + K) / 2 := by

  -- prove (N ^ 2 + K - 1) * (N ^ 2 + K) is Even number
  have : Even ((N ^ 2 + K) * ((N ^ 2 + K) - 1)) := by
    exact Nat.even_mul_pred_self (N ^ 2 + K)
  -- calculate the N^2+K-1 th triangular number
  unfold T
  rw [show N ^ 2 + K - 1 + 1 = N ^ 2 + K by omega]