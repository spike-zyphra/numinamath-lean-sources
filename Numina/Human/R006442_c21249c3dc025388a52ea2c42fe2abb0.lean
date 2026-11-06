import Mathlib

def f (n: ℕ) : ℕ :=
  match n with
  | 0 => 2
  | 1 => 3
  | n + 2 => (f n * f (n + 1)) % 10

/-Let j be a non-negative integer. A sequence f of natural numbers is defined by
f(0)=2, f(1)=3, and
f(n+2)=(f(n)⋅f(n+1))(mod10) for all n≥0.
Determine the value of f(6j). Show that the answer is 2.-/

theorem number_theory_637094 (j: ℕ): f (6 * j) = 2 := by

  -- we show that f is 6-periodic
  have p: ∀ n, 2 ≤ n → f (n + 6) = f n := by
    intro n hn
    induction' n using Nat.strongRecOn with n ih
    by_cases l: n < 4
    .
      interval_cases n
      .
        simp [f]
      .
        simp [f]
    .
      replace l: 4 ≤ n := by omega
      clear hn
      rw [show n + 6 = n + 4 + 2 by omega]
      rw [f]
      have s1:= ih (n - 1) (by omega) (by omega)
      have s2:= ih (n - 2) (by omega) (by omega)
      rw [show n - 1 + 6 = n + 5 by omega] at s1
      rw [show n - 2 + 6 = n + 4 by omega] at s2
      rw [show n + 4 + 1 = n + 5 by omega]
      rw [s1, s2]
      nth_rewrite 3 [show n = n - 2 + 2 by omega]
      rw [f]
      rw [show n - 2 + 1 = n - 1 by omega]

  -- then we can show that f(6j) = 2 for 1 ≤ j
  have q: ∀ j, 1 ≤ j → f (6 * j) = 2 := by
    intro j hj
    induction' j with j ih
    .
      simp [f]
    .
      by_cases l: j = 0
      .
        simp [l, f]
      .
        rw [show 6 * (j + 1) = 6 * j + 6 by omega]
        specialize p (6 * j) (by omega)
        rw [p]
        have s: 1 ≤ j := by omega
        simp [s] at ih
        tauto

  -- finally we can conclude
  by_cases r: j = 0
  .
    simp [r, f]
  .
    replace r: 1 ≤ j := by omega
    specialize q j r
    tauto