import Mathlib

open Finset

/- Define a function $A(m, n)$ by \[ A(m,n) = \left\{ \begin{aligned} &n+1& \text{ if } m = 0 \\ &A(m-1, 1) & \text{ if } m > 0 \text{ and } n = 0 \\ &A(m-1, A(m, n-1))&\text{ if } m > 0 \text{ and } n > 0. \end{aligned} \right.\]Compute $A(2, 1).$ -/
theorem algebra_11610 {A : ℕ → ℕ → ℕ}
    (hA : ∀ m n, A m n = if m = 0 then n + 1 else (if n = 0 then A (m - 1) 1 else A (m - 1) (A m (n - 1))))
    : A 2 1 = 5 := by
  simp [hA]