import Mathlib

open Real
/-
Which is larger,

$$
3^{3^{3^{3}}} \text { or } 2^{2^{2^{2^{2}}}} ?
$$

Remark. Note that $3^{3^{3}}$ means $3^{\left(3^{3}\right)}$, not $\left(3^{3}\right)^{3}$ and so on.
-/

theorem number_theory_254057 :
  3^(3^(3^3)) > 2^(2^(2^(2^2))) := by

  --We simplify our expressions.
  have e1: 3^(3^(3^3)) = 3^(3^27) := by 
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num]
  have e2: 2^(2^(2^(2^2))) = 2^(2^16) := by 
    rw [show ((2 : ℕ) ^ (2 ^ (2 ^ 2))) = 2 ^ 16 by norm_num]
  rw [e1,e2]

  --Then, the claim follows from the following three inequalities, which are corrolaeries of facts like "exponentiation is non-decreasing."
  have l1 : 3^(3^16) < 3^(3^27) := by
    apply pow_lt_pow_right₀
    linarith
    apply pow_lt_pow_right₀
    linarith
    linarith
  have l2 : 3^(2^16) < 3^(3^16) := by 
    apply pow_lt_pow_right₀
    linarith
    apply pow_lt_pow_left₀
    linarith
    linarith
    norm_num
  have l3 : 2^(2^16) < 3^(2^16) := by
    apply pow_lt_pow_left₀
    linarith
    linarith
    exact Ne.symm (Nat.zero_ne_add_one 65535)
  
  calc
    2^(2^16) < 3^(2^16) := l3
    _ < 3^(3^16) := l2
    _ < 3^(3^27) := l1
  