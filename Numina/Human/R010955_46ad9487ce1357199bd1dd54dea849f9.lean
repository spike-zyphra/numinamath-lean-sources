import Mathlib

open Finset

/- Define $\phi^{!}(n)$ as the product of all positive integers less than or equal to $n$ and relatively prime to $n$. -/
def φ! (n : ℕ) : ℕ :=
    ∏ x ∈ {x ∈ Icc 1 n | Nat.Coprime x n}, x

/- Define $\phi^{!}(n)$ as the product of all positive integers less than or equal to $n$ and relatively prime to $n$. Compute the remainder when

$$
\sum_{\substack{2 \leq n \leq 50 \\ \operatorname{gcd}(n, 50)=1}} \phi^{!}(n)
$$

is divided by 50 . -/
theorem number_theory_609535 :
    (∑ n ∈ {n ∈ Icc 2 50 | Nat.gcd n 50 = 1}, φ! n) % 50 = 12 := by
  -- The sum is 5502770116386224610253297124060125740347113195606901065362, which can be computed directly.
  native_decide
