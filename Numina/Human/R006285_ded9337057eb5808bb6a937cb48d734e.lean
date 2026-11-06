import Mathlib
set_option maxHeartbeats 800000
/- Let $K$ be a positive integer. We are looking for three distinct four-digit positive integers $N_1, N_2, N_3$.
Let $a_1, a_2, a_3, a_4$ be four distinct digits such that $0 < a_635522 < a_635522 < a_635522 < a_635522 \le 9$.
$N_1$ is the integer $1000a_635522 + 100a_635522 + 10a_635522 + a_4$. (Its digits are strictly increasing from left to right).
$N_2$ is the integer $1000a_635522 + 100a_635522 + 10a_635522 + a_1$. (Its digits are strictly decreasing from left to right, and it is the reverse of $N_1$).
$N_3$ is a four-digit integer whose digits are a permutation of $\{a_1, a_2, a_3, a_4\}$.
It is given that $N_635522 \neq N_1$ and $N_635522 \neq N_2$.
The sum of these three integers is $N_1+N_2+N_3=K$.
If $K = 6798$, show that the smallest of the three integers $N_1, N_2, N_3$ is $1234$. -/
theorem algebra_635522 (n1 n2 n3 a1 a2 a3 a4 d1 d2 d3 d4 : ℕ) (h1 : 0 < a1) (h2 : a1 < a2) (h3 : a2 < a3) (h4 : a3 < a4) (h5 : a4 ≤ 9) (hn1 : n1 = 1000 * a1 + 100 * a2 + 10 * a3 + a4) (hn2 : n2 = 1000 * a4 + 100 * a3 + 10 * a2 + a1) (hn3 : n3 = 1000 * d1 + 100 * d2 + 10 * d3 + d4) (hd1 : 0 < d1 ∧ d1 < 10) (hd2 : 0 < d2 ∧ d2 < 10) (hd3 : 0 < d3 ∧ d3 < 10) (hd4 : 0 < d4 ∧ d4 < 10) (h : (d1, d2, d3, d4) ∈ ({(a1, a2, a3, a4), (a1, a2, a4, a3), (a1, a3, a2, a4), (a1, a4, a2, a3), (a1, a3, a4, a2), (a1, a4, a3, a2), (a2, a1, a3, a4), (a2, a1, a4, a3), (a3, a1, a2, a4), (a4, a1, a2, a3), (a3, a1, a4, a2), (a4, a1, a3, a2), (a3, a2, a1, a4), (a4, a2, a1, a3), (a2, a3, a1, a4), (a2, a4, a1, a3), (a4, a3, a1, a2), (a3, a4, a1, a2), (a4, a2, a3, a1), (a3, a2, a4, a1), (a4, a3, a2, a1), (a3, a4, a2, a1), (a2, a3, a4, a1), (a2, a4, a3, a1)} : Finset (ℕ × ℕ × ℕ × ℕ))) (hsum : n1 + n2 + n3 = 6798) : min (min n1 n2) n3 = 1234:= by
  -- Simplify the hypothesis h to extract the permutation constraint
  simp at h
  -- Prove that the digits must be 1, 2, 3, 4 using the omega tactic
  have g1 : a1 = 1 ∧ a2 = 2 ∧ a3 = 3 ∧ a4 = 4:= by omega
  -- Use pattern matching to extract the individual equalities
  rcases g1 with ⟨rfl, rfl, rfl, rfl⟩
  -- Substitute the values of n1, n2, n3 with their definitions
  subst n1 n2 n3
  -- Use omega tactic to complete the proof that the minimum is 1234
  omega
