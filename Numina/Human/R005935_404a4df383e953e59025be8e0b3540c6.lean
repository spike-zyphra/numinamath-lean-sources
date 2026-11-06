import Mathlib

open Finset

/-For any positive integer n, let f(n) be the number of ordered triples (a,b,c) of positive integers such that
max (a,b,c) divides n and
gcd(a,b,c)=1.
Compute f(1)+f(2)+⋯+f(100).-/

theorem combinatorics_610809: ∑ n ∈ Icc 1 100,
  ((Icc 1 n ×ˢ Icc 1 n ×ˢ Icc 1 n).filter (fun (a, b, c) => max a (max b c) ∣ n ∧ (a.gcd b).gcd c = 1)).card = 1000000 := by

    native_decide