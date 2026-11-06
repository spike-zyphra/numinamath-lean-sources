import Mathlib

def F (n : Nat) : Nat :=
  if n % 3 == 2 then n / 3
  else if n % 3 == 1 then n / 3 - 1
  else n / 3 - 2

/-"For a positive integer $N \ge 20$, let $f(n, k)$ be the remainder when $n$ is divided by $k$. For $n > 1$,
let $F(n) = \max_{1 \le k \le \lfloor n/2 \rfloor} f(n, k)$. It is known that for $m = \lfloor n/3 \rfloor$,
$F(n)$ equals $m$ if $n=3m+2$, $m-1$ if $n=3m+1$ (for $m \ge 1$), and $m-2$ if $n=3m$ (for $m \ge 2$).
Let $S(N) = \sum_{n=20}^N F(n)$.
The sum can be calculated as $S(N) = S_1 + S_2 + S_3$, where:
Let $m_{20} = \lfloor 20/3 \rfloor = 6$ and $m_N = \lfloor N/3 \rfloor$.
$S_1 = \sum_{n=20}^{\min(N, 3m_{20}+2)} F(n)$. (This is $F(20)$ if $N \ge 20$, as $20 = 3 \cdot 6 + 2$.)
$S_2 = \sum_{j=m_{20}+1}^{m_N-1} (3j-3)$. (This sum is 0 if $m_N-1 < m_{20}+1$, i.e. $m_N \le m_{20}+1$.)
$S_3 = \sum_{n=3m_N}^N F(n)$. (This sum is empty if $N < 3m_N$, which is not possible. It includes terms $F(3m_N), F(3m_N+1), \dots, F(N)$.)
If $N=40$, find $S(N) \pmod{1000}$. Show the answer is $182$."
-/

theorem number_theory_641069: (∑ i ∈ Finset.Icc 20 40, F i) % 1000 = 182 := by

  simp [Finset.sum_Icc_succ_top, F]