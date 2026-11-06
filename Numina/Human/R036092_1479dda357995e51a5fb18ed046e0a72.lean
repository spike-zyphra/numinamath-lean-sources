import Mathlib

open Nat 

def G (n : ℕ) := fib (3 * n)

/- The Fibonacci numbers are defined recursively by the equation
\[ F_n = F_{n - 1} + F_{n - 2}\]for every integer $ n \ge 2$, with initial values $ F_0 = 0$ and $ F_1 = 1$.  Let $ G_n = F_{3n}$ be every third Fibonacci number.  There are constants $ a$ and $ b$ such that every integer $ n \ge 2$ satisfies
\[ G_n = a G_{n - 1} + b G_{n - 2}.\]Find $(a,b)$. -/
theorem algebra_21722 {a b : ℤ} (ha : ∀ n ≥ 2, G n = a * G (n - 1) + b * G (n - 2)) :
    a = 4 ∧ b = 1 := by
  have h1 := ha 2 (by decide)
  have h2 := ha 3 (by decide)
  simp [G, fib] at h1 h2
  constructor <;> omega