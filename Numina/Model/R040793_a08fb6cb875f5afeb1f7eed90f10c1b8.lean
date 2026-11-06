import Mathlib

open Nat
open Finset

/-
Let $n=p_{1}^{\alpha_{1}} \ldots p_{s}^{\alpha_{s}}$.
Prove the equality
$\varphi(n)=n\left(1-1 / p_{1}\right) \ldots\left(1-1 / p_{s}\right)$.

a) using the multiplicativity of the Euler function;
b) using the inclusion-exclusion principle.

Prove the Gauss identity $\sum_{d \mid n} \varphi(d)=n$.

The definition of the function $\varphi(n)$
is given in problem $\underline{60758}$.
-/

-- Annotator's note: I'm proving Euler's product formula only by multiplicativity
-- (skipping the inclusion / exclusion proof, too difficult to formalize),
-- and proving a simpler formulation that doesn't require denoms / rational numbers.
-- Also I'm proving the Gauss identity.
theorem number_theory_219842 {n : ℕ} :
    (n.totient * ∏ p ∈ n.primeFactors, p) =
      n * ∏ p ∈ n.primeFactors, (p - 1) ∧ -- first equality, written more simply
    n.divisors.sum totient = n := by 
  constructor
  · -- Show that `n.totient * ∏ p ∈ n.primeFactors, p = n * ∏ p ∈ n.primeFactors, (p - 1)`
    rw [Nat.totient_mul_prod_primeFactors]
  · -- Show that the sum of Euler's totient function over divisors equals n
    have h2 : n.divisors.sum totient = n := by
      apply Nat.sum_totient
    exact h2