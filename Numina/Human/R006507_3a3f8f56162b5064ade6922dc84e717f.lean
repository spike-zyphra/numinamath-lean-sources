import Mathlib

def M : Nat := 3^(3^2)

/-Let $A_k$ denote the $k$-th iterated power of 2,
defined by $A_1 = 2$ and $A_{i+1} = 2^{A_i}$ for $i \ge 1$. (So $A_2 = 2^2=4$, $A_3 = 2^{2^2}=16$, and so on).
Let $M = 3^{(3^2)}$.

Theorem: $A_3 < M$ and $A_4 > M$.-/

theorem number_theory_637841: 2 ^ (2 ^ 2) < M ∧ 2 ^ (2 ^ (2 ^ 2)) > M := by

  simp [M]