import Mathlib

/- Prove that for each positive integer $k$ there exists a number base $b$ along with $k$ triples of Fibonacci numbers $(F_u,F_v,F_w)$ such that when they are written in base $b$, their concatenation is also a Fibonacci number written in base $b$. (Fibonacci numbers are defined by $F_1 = F_2 = 1$ and $F_{n+2} = F_{n+1} + F_n$ for all positive integers $n$.)


[i]Proposed by Serbia[/i] -/
theorem number_theory_62389 (k : ℕ) (hk : 0 < k) :
    ∃ b : ℕ, ∀ i ∈ Finset.range k, ∃ u v w : ℕ,
      Nat.fib u > 0 ∧ Nat.fib v > 0 ∧ Nat.fib w > 0 ∧
      Nat.fib (u + v + w) = Nat.fib u * b ^ (Nat.fib v) + Nat.fib v * b ^ (Nat.fib w) := by 
  use 1
  intro i hi
  use 1
  use 1
  use 1
  aesop
