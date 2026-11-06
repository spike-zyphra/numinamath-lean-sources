import Mathlib
/- Let $N$ be a positive integer. Let $L_N$ denote the least common multiple of the first $N$ positive integers.
Suppose $N=16$.
Suppose that $L_N$ is equal to the number $7A0BC0_{10}$ (where $A$ is the digit at the $10^4$ position, $B$ is the digit at the $10^2$ position, and $C$ is the digit at the $10^1$ position). The digits $A, B, C$ are single digits from $0$ to $9$.
This number $7A0BC0_{10}$ corresponds to the formal representation $\text{Nat.ofDigits 10 } [0, C, B, 0, A, 7]$.
Determine the value of $100A + 10B + C$. Show the answer is $272$. -/
theorem number_theory_637579 (A B C : ℕ) (hA : A ≤ 9) (hB : B ≤ 9) (hC : C ≤ 9) (h : Nat.lcm 16 (Nat.lcm 15 (Nat.lcm 14 (Nat.lcm 13 (Nat.lcm 12 (Nat.lcm 11 (Nat.lcm 10 (Nat.lcm 9 (Nat.lcm 8 (Nat.lcm 7 (Nat.lcm 6 (Nat.lcm 5 (Nat.lcm 4 (Nat.lcm 3 (Nat.lcm 2 1)))))))))))))) = 7 * 10 ^ 5 + A * 10 ^ 4 + B * 10 ^ 2 + C * 10) : 100 * A + 10 * B + C = 272:= by
  -- First step involves computing LCM for N = 16 as described in problem statement.
  norm_num at h
  -- use omega to finish the proof
  omega
