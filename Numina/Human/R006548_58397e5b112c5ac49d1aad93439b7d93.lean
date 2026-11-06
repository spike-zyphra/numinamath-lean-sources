import Mathlib

/-
Let $k$ be a positive integer. Let $N$ be a natural number.
Theorem: If $N=81$ and $k=1$, then $N$ is a two-digit number (in base 10), and if $S$ is the sum of the digits of $N$, then $k N = S^2$.
-/

theorem number_theory_638395 (k : ℕ) (N : ℕ) (Ne : N = 81) (ke : k = 1) (S : ℕ) (hS: S = (Nat.digits 10 N).sum):
(Nat.digits 10 N).length = 2 ∧ k * N = S^2 := by
  
  rw [hS, Ne, ke]
  norm_num