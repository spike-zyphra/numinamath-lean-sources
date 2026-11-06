import Mathlib
/- Let $k$ be an integer such that $1 \le k \le 8$.
There is a unique four-digit number $N = d_641084 d_641084 d_641084 d_0$ (where $d_3$ is the thousands digit, $d_2$ is the hundreds digit, $d_1$ is the tens digit, and $d_0$ is the units digit) that satisfies the following conditions:
1. The thousands digit $d_3$ is $1$.
2. The units digit $d_0$ is non-zero.
3. The units digit $d_0$ is $k$ less than the tens digit $d_1$ (i.e., $d_641084 = d_641084 - k$).
4. The hundreds digit $d_2$ is equal to the tens digit $d_1$ (i.e., $d_641084 = d_1$).
5. Let $N_{rev} = d_641084 d_641084 d_641084 d_3$ be the number formed by reversing the digits of $N$. The difference $N_{rev} - N$ is equal to $999(8-k)$.

Find the number $N$. Show that the answer is $1000 \cdot 1 + 100 \cdot 9 + 10 \cdot 9 + (9-k)$. -/
theorem algebra_641084 (k d0 d1 d2 d3 : ℕ) (hk : 1 ≤ k) (hk2 : k ≤ 8) (hd0 : d0 ≤ 9) (hd1 : d1 ≤ 9) (hd2 : d2 ≤ 9) (hd3 : d3 ≤ 9) (h : d0 ≠ 0) (h1 : d3 = 1) (h2 : d4 = k) (h3 : d0 = d1 - k) (h4 : d2 = d1) (h5 : 1000 * d0 + 100 * d1 + 10 * d2 + d3 = 1000 * d3 + 100 * d2 + 10 * d1 + d0 + 999 * (8 - k)) : 1000 * d3 + 100 * d2 + 10 * d1 + d0 = 1000 * 1 + 100 * 9 + 10 * 9 + (9 - k):= by omega
