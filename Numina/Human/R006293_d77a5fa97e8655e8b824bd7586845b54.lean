import Mathlib

def a (n : Nat) : Nat :=
  if n = 0 then 1
  else if n = 1 then 2
  else a (n - 2) + (a (n - 1))^2

def R (n: Nat) : Nat :=
  match n % 10 with
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 6
  | 4 => 6
  | 5 => 0
  | 6 => 6
  | 7 => 1
  | 8 => 0
  | _ => 1

/-Let $k$ be a non-negative integer. Let the sequence $a_n$ be defined by $a_0=1$, $a_1=2$, and for $n > 1$, $a_n = a_{n-2} + (a_{n-1})^2$.
Let $R_S$ be the list of integers $(1, 2, 5, 6, 6, 0, 6, 1, 0, 1)$.
Show that the remainder when $a_k$ is divided by $7$ is equal to $R_S[k \pmod{10}]$, where $R_S[j]$ denotes the $j$-th element (0-indexed) of the sequence $R_S$.-/

theorem number_theory_635607: a k % 7 = R (k % 10) := by
  induction' k using Nat.strongRecOn with n ih
  by_cases l: n < 2

  -- base case
  .
    interval_cases n
    .
      simp [a, R]
    .
      simp [a, R]

  -- inductive case
  .
    simp at l
    replace l: n ≠ 0 ∧ n ≠ 1 := by
      omega
    rw [a]
    simp [l]
    rw [Nat.add_mod, Nat.pow_mod]
    have f1:= ih (n - 1) (by omega)
    have f2:= ih (n - 2) (by omega)
    rw [f1, f2]
    clear f1 f2
    rw [show n - 1 = n - 2 + 1 by omega]
    nth_rewrite 3 [show n = n - 2 + 2 by omega]
    set k:= n - 2
    clear ih l
    clear_value k
    rw [show (k + 1) % 10 = (k % 10 + 1) % 10 by simp [Nat.add_mod]]
    rw [show (k + 2) % 10 = (k % 10 + 2) % 10 by simp [Nat.add_mod]]
    set q:= k % 10
    have lq: q < 10 := by
      omega
    interval_cases q
    all_goals simp [R]