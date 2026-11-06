import Mathlib

def f (n: Nat): Nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | n + 2 => f (n + 1) + f n

/-Let $f(n)$ be a sequence of natural numbers defined by
$f(0)=1$, $f(1)=1$, and $f(n+2) = f(n) + f(n+1)$ for all $n \ge 0$.
Let $k$ be a non-negative integer. Determine the remainder when $f(24k+22)$ is divided by $12$.
Show the answer is $1$.-/

theorem number_theory_637117 (k: ℕ): f (24 * k + 22) % 12 = 1 := by

  -- we show that the sequence is periodic modulo 24
  have h: ∀ n, f (n + 24) % 12 = f n % 12 := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    by_cases l: n < 2
    .
      interval_cases n
      .
        simp [f]
      .
        simp [f]
    .
      simp at l
      rw [show n + 24 = n + 22 + 2 by ring]
      rw [f]
      have f1:= ih (n - 1) (by omega)
      have f2:= ih (n - 2) (by omega)
      rw [show n - 1 + 24 = n + 23 by omega] at f1
      rw [show n - 2 + 24 = n + 22 by omega] at f2
      rw [show n + 22 + 1 = n + 23 by omega]
      rw [Nat.add_mod]
      rw [f1, f2]
      nth_rewrite 3 [show n = n - 2 + 2 by omega]
      rw [f]
      nth_rewrite 2 [Nat.add_mod]
      rw [show n - 2 + 1 = n - 1 by omega]


  -- then we can give the value of f (24 * k + 22) % 12
  induction' k with k ih
  .
    simp [f]
  .
    rw [show 24 * (k + 1) + 22 = 24 * k + 22 + 24 by ring]
    specialize h (24 * k + 22)
    simp [ih, h]
