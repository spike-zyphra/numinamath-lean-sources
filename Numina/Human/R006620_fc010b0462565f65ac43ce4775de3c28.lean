import Mathlib

/-
Let $a, b, c, d, n$ be natural numbers and let $k$ be a positive natural number. If $k$ divides $a n+b$ and $k$ divides $c n+d$, prove that $k$ divides $a d - b c$.
-/

theorem number_theory_638294 (a b c d n k: ℕ) (kpos: 0 < k)
(h1: k ∣ a*n+b) (h2: k ∣ c*n+d):
(k:ℤ) ∣ (a:ℤ)*d-b*c := by

  --We multiply an+b by c and multiply cn+d by a and then substract these two equations to get k|(ad-bc).
  have t1: k ∣ c* (a*n+b) := by exact Dvd.dvd.mul_left h1 c 
  have t2: k ∣ a* (c*n+d) := by exact Dvd.dvd.mul_left h2 a
  zify at t1 t2
  have t3 : (k:ℤ) ∣ ((↑c * (↑a * ↑n + ↑b)) - (↑a * (↑c * ↑n + ↑d))) := by exact Int.dvd_sub t1 t2
  have : ((↑c * (↑a * ↑n + ↑b)) - (↑a * (↑c * ↑n + ↑d))) = - ((a:ℤ)*d-b*c) := by ring_nf
  rw [this] at t3
  exact Int.dvd_neg.mp t3