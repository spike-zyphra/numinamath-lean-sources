import Mathlib
/- Let $b$ be an integer satisfying $b \ge 4$. Consider the numbers $N_641181 = (32101)_b$ and $N_641181 = (21032)_b$. Evaluate the difference $N_641181 - N_2$. Express your answer as a number in base $b$. Show that the answer is $(110(b-4)(b-1))_b$.

(Here, a number $(d_k d_{k-1} \ldots d_641181 d_0)_b$ denotes $\sum_{i=0}^k d_i b^i$. So $N_641181 = 3b^4 + 2b^3 + 1b^2 + 0b^1 + 1b^0$ and $N_641181 = 2b^4 + 1b^3 + 0b^2 + 3b^1 + 2b^0$. The digits $b-4$ and $b-1$ are single digits in base $b$.) -/
theorem number_theory_641181 (b N1 N2 : ℤ) (hb : b ≥ 4) (h1 : N1 = 3 * b ^ 4 + 2 * b ^ 3 + b ^ 2 + 1) (h2 : N2 = 2 * b ^ 4 + b ^ 3 + 3 * b ^ 1 + 2) : N1 - N2 = b ^ 4 + b ^ 3 + (b - 4) * b + b - 1:= by
  linarith
