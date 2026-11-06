import Mathlib

/- Let $d_1, d_2, d_3, d_4$ be specified digits, and let $K_0$ be the integer $1000 d_4 + 100 d_3 + 10 d_2 + d_1$.
Consider a six-digit number $N$ of the form $x d_4 d_3 d_2 d_1 y$, where $x$ is the first digit and $y$ is the last digit. The numerical value of $N$ is $100000x + 10K_0 + y$.
Suppose $N$ is a multiple of an integer $M$. The digits $x, y$ must satisfy $x \in \{1, \ldots, 9\}$ and $y \in \{0, \ldots, 9\}$.
Let $R_x = 100000 \pmod M$ and $R_K = (10K_0) \pmod M$.
Assume that there is a unique integer $j$ such that $jM$ is in the range $[R_x \cdot 1 + R_K + 0, R_x \cdot 9 + R_K + 9]$, and that values $x_0, y_0$ satisfying $R_x x_0 + R_K + y_0 = jM$ are uniquely determined.
Show that the quotient $N/M$ is $\frac{100000x_0 + 10K_0 + y_0}{M}$.

Let's make it more concrete by fixing $M=99$ as in the original problem.
Let $d_1, d_2, d_3, d_4$ be specified digits, and let $K_0$ be the integer $1000 d_4 + 100 d_3 + 10 d_2 + d_1$.
A six-digit number $N$ is written as $x d_4 d_3 d_2 d_1 y$, where $x$ is the first digit ($x \in \{1, \ldots, 9\}$) and $y$ is the last digit ($y \in \{0, \ldots, 9\}$). The value of $N$ is $100000x + 10K_0 + y$.
Suppose $N$ is a multiple of $99$. Let $R_K = (10K_0) \pmod{99}$. Assume $R_K \le 89$. (This ensures that $10x+y = 99-R_K$ yields $x \ge 1$.)
The digits $x$ and $y$ are determined by the condition $10x + y = 99 - R_K$.
Show that the quotient $N/99$ is $1010x + \lfloor 10K_0/99 \rfloor + 1$. -/
theorem number_theory_641417
  (d : Fin 4 → ℕ)
  (K : ℕ)
  (hK : K = 1000 * d 3 + 100 * d 2 + 10 * d 1 + d 0)
  : ∀ N > 0 ,
    ∀ x y, N = 100000 * x + 10 * K + y → 1 ≤ x → x ≤ 9 → 0 ≤ y → y ≤ 9
    → let Rₖ := (10 * K) % 99;
      Rₖ ≤ 89 → 10 * x + y + Rₖ = 99 →
    N / 99 = 1010 * x + 10 * K / 99 + 1 :=
by
  rintro N Npos x y hN1 xpos xup ypos yu R Ru hR
  conv =>
    rhs
    rw [←Nat.mul_div_cancel (1010 * x + 10 * K / 99 + 1) (n := 99) (by simp)]
  congr
  simp [R] at hR
  have H : N = (1010 * x + 10 * K / 99 + (10 * x + y + R)/99) * 99 := by
    omega
  have : N ≡ 0 [MOD 99] := by
      simp [Nat.ModEq]
      omega
  have : (10 * x + y + R)/99 = 1 := by omega
  rw [this] at H
  omega
