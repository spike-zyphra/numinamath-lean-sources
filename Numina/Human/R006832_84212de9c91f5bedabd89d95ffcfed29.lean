import Mathlib

/-Let $Y$ be an integer greater than 1. Suppose that $p_Y = 2Y^2 - 2Y + 1$ and $q_Y = 2Y^2 + 2Y + 1$ are prime numbers.
Let $n = 4Y^4+1$.
Theorem: Given the integer $n$, there exist prime numbers $p, q$ such that $p \cdot q = n$.
Show that these primes are $p_Y$ and $q_Y$ (in some order).-/

theorem number_theory_641577 (Y pX pY n: ℤ) (h1: pY = 2 * Y^2 - 2 * Y + 1)
(h2: pX = 2 * Y^2 + 2 * Y + 1) (h3: n = 4 * Y^4 + 1) (hp: Prime pX) (hq: Prime pY) :
    ∃ p q : ℤ, Prime p ∧ Prime q ∧ p * q = n := by

    use pX, pY
    simp [hp, hq]
    simp [h1, h2, h3]
    ring

