import Mathlib
/- Let $m$ be a positive integer such that $6$ divides $m$. Show that for any integer $n$, if $n$ is divisible by $m$, then $n$ can be expressed as the sum of four integer cubes. -/
theorem number_theory_636788 (m n : ℤ) (hm : m > 0) (h : 6 ∣ m) (hn : m ∣ n) : ∃ x1 x2 x3 x4 : ℤ, n = x1 ^ 3 + x2 ^ 3 + x3 ^ 3 + x4 ^ 3:= by
  -- First, use transitivity of divisibility: if 6|m and m|n, then 6|n
  replace hn : 6 ∣ n:= by exact Int.dvd_trans h hn
  -- Let k be the integer such that n = 6k
  rcases hn with ⟨k, rfl⟩
  -- Construct the four cubes: (k+1)³ + (k-1)³ + (-k)³ + (-k)³
  use (k + 1), (k - 1), -k, -k
  -- Simplify the expression using ring arithmetic
  ring
