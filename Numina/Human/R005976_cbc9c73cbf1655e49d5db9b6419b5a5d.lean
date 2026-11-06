import Mathlib
open Nat Finset

/-Find an $n$ such that $n!-(n-1)!+(n-2)!-(n-3)!+\cdots \pm 1$ ! is prime. Be prepared to justify your answer for $\left\{\begin{array}{c}n, \\ {\left[\frac{n+225}{10}\right],} \\ n \leq 25\end{array}\right.$ points, where $[N]$ is the greatest integer less than $N$.-/
theorem number_theory_610949 : 
  letI Sn (n : ℕ) : ℤ :=
  let terms := List.range (n - 1 + 1) -- creates [0, 1, ..., n-1]
  List.foldl (fun acc k =>
    let term_val := (factorial (n - k) : ℤ)
    if Even k then acc + term_val else acc - term_val
  ) 0 terms
  ∃ n, Nat.Prime (Sn n).toNat := by
  use 3
  native_decide