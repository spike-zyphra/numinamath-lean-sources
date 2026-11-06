import Mathlib
/- Let $b$ be an integer such that $b \ge 5$. Let $N_1$ be the number whose representation in base $b$ is $1121_b$, which means $N_640775 = 1 \cdot b^3 + 1 \cdot b^2 + 2 \cdot b^1 + 1 \cdot b^0$. Let $N_2$ be the number whose representation in base $b$ is $12_b$, which means $N_640775 = 1 \cdot b^1 + 2 \cdot b^0$. Determine the quotient of the Euclidean division of $N_1$ by $N_2$. Show that this quotient, when expressed in base $b$, is $(b-1)3_b$ (that is, the number whose most significant digit is $b-1$ and whose least significant digit is $3$). -/
theorem number_theory_640775 (b N1 N2 : ℕ) (hb : b ≥ 5) (h1 : N1 = b ^ 3 + b ^ 2 + 2 * b + 1) (h2 : N2 = b + 2) : N1 / N2 = (b - 1) * b + 3:= by
  -- Substitute the values of N1 and N2
  subst N1 N2
  -- Define c as b - 5 for easier manipulation
  set c:= b - 5 with hc
  -- Clear the value of c from the context
  clear_value c
  -- Replace b with c + 5 using omega tactic
  replace hc : b = c + 5:= by omega
  -- Substitute b with c + 5
  subst b
  -- Use Nat.div_eq_of_lt_le to prove the division equation
  refine Nat.div_eq_of_lt_le ?_ ?_
  .
    -- First goal: Simplify c + 5 - 1 to c + 4 using omega
    rw [show c + 5 - 1 = c + 4 by omega]
    -- Normalize ring expressions
    ring_nf
    -- Solve linear arithmetic
    linarith
  .
    -- Second goal: Similar steps as above
    rw [show c + 5 - 1 = c + 4 by omega]
    ring_nf
    linarith
