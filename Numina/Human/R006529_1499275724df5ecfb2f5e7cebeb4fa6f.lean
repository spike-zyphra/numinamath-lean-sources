import Mathlib

/-Let $N$ be a three-digit positive integer. Let $A$ also be a three-digit positive integer.
Let $H_A$ denote the hundreds digit of $A$ (i.e., $H_A = A \operatorname{div} 100$) and
$T_A$ denote the integer formed by the last two digits of $A$ (i.e., $T_A = A \pmod{100}$).
Define an auxiliary number $X_A = 100 \cdot T_A + H_A$. If the equation $N \cdot 1000 + X_A = A \cdot 1000 + X_A$ holds,
show that $A=N$.-/

theorem number_theory_638073 (N A X_A: ℕ)
  (h3: N * 1000 + X_A = A * 1000 + X_A): A = N := by
    omega
