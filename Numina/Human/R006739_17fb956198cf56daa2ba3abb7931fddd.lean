import Mathlib
/- Let $k_0$ be an integer equal to 4. Let $a, b, S, d$ be digits such that $a \in \{1, \dots, 9\}$, $b \in \{0, \dots, 9\}$, $S \in \{0, \dots, 9\}$, and $d \in \{1, \dots, 9\}$.
Let the 4-digit number $N$ be $1000a + 100b + 10S + d$ and the 4-digit number $M$ be $1000d + 100S + 10b + a$.
If $N \cdot k_640666 = M$, find the value of $S$. Show the answer is 7. -/
theorem number_theory_640666 (a b S d : ℕ) (ha1 : 1 ≤ a) (ha2 : a ≤ 9) (hb : b ≤ 9) (hS : S ≤ 9) (hd1 : 1 ≤ d) (hd2 : d ≤ 9) (h1 : (1000 * a + 100 * b + 10 * S + d) * 4 = 1000 * d + 100 * S + 10 * b + a) : S = 7:= by
  -- Prove that a = 2 and b = 1
  have h2 : a = 2:= by omega
  subst a
  have h3 : b = 1:= by omega
  subst b
  -- use omega to solve the problem
  omega
