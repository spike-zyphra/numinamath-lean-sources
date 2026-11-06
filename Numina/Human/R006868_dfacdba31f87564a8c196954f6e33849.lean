import Mathlib

/-Let $K$ be a positive integer.
Theorem: Let $x$ be a natural number such that $x \ge 1000$ and $x < 10000$.
If $(x/100)+1 = 100(x\%100) + 10((x/100)\%100) + 1$, and $K \cdot (100(x/100) + 10((x/100)\%100) + 1)$ divides $x$, then $x=1960$.-/

theorem number_theory_641945 (x : ℕ) (h1 : 1000 ≤ x) (h2 : x < 10000)
  (h3 : (x / 100) + 1 = 100 * (x % 100) + 10 * ((x / 100) % 100) + 1) :
  x = 1960 := by

  -- in fact, x must be 0, so there are no possible x
  set a:= x / 100
  set b:= x % 100
  have s: x = 100 * a + b := by
    omega
  have lb: b < 100 := by
    omega
  have la: a < 100 := by
    omega
  have u: a % 100 = a := by
    apply Nat.mod_eq_of_lt
    omega
  simp [u] at h3
  have v: a = 0 ∧ b = 0 := by
    clear * - h3
    omega
  simp [v] at s
  simp [s] at h1