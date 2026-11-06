import Mathlib

/- Soit $a_{1}, a_{2}, \ldots$ la suite d'entiers telle que $a_{1}=1$ et, pour tout entier $n \geqslant 1$,

$$
a_{n+1}=a_{n}^{2}+a_{n}+1
$$

Démontrer, pour tout entier $n \geqslant 1$, que $a_{n}^{2}+1$ divise $a_{n+1}^{2}+1$. -/
theorem number_theory_111051 {a : ℕ → ℤ} (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = a n ^ 2 + a n + 1) :
    ∀ n ≥ 1, (a n) ^ 2 + 1 ∣ (a (n + 1)) ^ 2 + 1 := by
  -- Let x = a n, then a (n + 1) = x ^ 2 + x + 1
  intro n hn
  rw [han _ hn]
  -- x ^ 2 + 1 ∣ (x ^ 2 + x + 1) ^ 2 + 1
  -- Because (x ^ 2 + 1) * (x ^ 2 + 2 * x + 2) = (x ^ 2 + x + 1) ^ 2 + 1
  use a n ^ 2 + 2 * a n + 2
  ring
