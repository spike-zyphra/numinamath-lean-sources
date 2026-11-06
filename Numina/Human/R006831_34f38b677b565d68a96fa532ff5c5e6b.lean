import Mathlib
/- Let $b$ be an integer greater than 4.
Let $N_1$ be the number whose representation in base $b$ is $4321_b$. This means $N_641575 = 4 \cdot b^3 + 3 \cdot b^2 + 2 \cdot b + 1$.
Let $N_2$ be the number whose representation in base $b$ is $123_b$. This means $N_641575 = 1 \cdot b^2 + 2 \cdot b + 3$.
Let $N_3$ be the number whose representation in base $b$ is $32_b$. This means $N_641575 = 3 \cdot b + 2$.
Let $N_4$ be the number whose representation in base $b$ is $21_b$. This means $N_641575 = 2 \cdot b + 1$.
Let $N_5$ be the number whose representation in base $b$ is $1_b$. This means $N_641575 = 1$.
Compute the value $X = N_641575 - N_641575 + N_641575 - N_641575 + N_5$. Show that the representation of $X$ in base $b$ is $4210_b$. -/
theorem number_theory_641575 (b N1 N2 N3 N4 N5 : ℕ) (hb : b > 4) (h1 : N1 = 4 * b ^ 3 + 3 * b ^ 2 + 2 * b + 1) (h2 : N2 = b ^ 2 + 2 * b + 3) (h3 : N3 = 3 * b + 2) (h4 : N4 = 2 * b + 1) (h5 : N5 = 1) : N1 - N2 + N3 - N4 + N5 = 4 * b ^ 3 + 2 * b ^ 2 + b:= by
  have g1 : b ^ 2 > 4 ^ 2:= by refine Nat.pow_lt_pow_left hb (by omega)
  -- prove the inequality via omega
  omega
