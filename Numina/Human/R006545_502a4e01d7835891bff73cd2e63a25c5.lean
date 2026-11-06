import Mathlib

/-Let $S$ be an integer satisfying $9 \le S \le 18$.
A number $N$ consists of three digits. Let these digits be $h$ (hundreds), $t$ (tens), and $u$ (units).
The sum of these digits is $S$. The digit in the units place is twice the digit in the hundreds place.
If 297 is added to $N$, the result is a number written with the same digits as $N$,
but in reverse order (i.e., if $N$ is $100h+10t+u$, the reversed number is $100u+10t+h$).
Show that $N = 100 \cdot 3 + 10 \cdot (S-9) + 6$.-/

theorem number_theory_638356 (N S h t u: ℤ)
  (h2: S = h + t + u) (h3: u = 2 * h) (h4: N = 100 * h + 10 * t + u) (h5: N + 297 = 100 * u + 10 * t + h):
  N = 100 * 3 + 10 * (S - 9) + 6 := by

    omega