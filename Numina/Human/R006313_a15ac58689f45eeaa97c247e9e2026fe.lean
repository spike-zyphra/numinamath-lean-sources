import Mathlib

def R (n: ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 3
  | 2 => 8
  | 3 => 4
  | 4 => 6
  | 5 => 2
  | 6 => 7
  | 7 => 0
  | 8 => 5
  | _ => 0

def a (n: ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | n + 3 => 2 * (a (n + 2) + a (n + 1))

/-Let N be a positive integer. A sequence of numbers an
(where n≥1) is defined by a1 = 1, a2 = 3 and for n≥3,
an =2 (a (n-1) + a (n-2))
Determine the remainder when the
N-th term a Nis divided by 9. Show that this remainder is
R j where j=(N−1)(mod9) and the sequence of possible remainders
(R0, ..., R8) is (1,3,8,4,6,2,7,0,5).-/

theorem number_theory_635786 (N: ℕ) (h: 1 ≤ N): a N % 9 = R ((N - 1) % 9) := by

  -- we show that a % 9 is 9-periodic
  have p: ∀ n, 1 ≤ n → a (n + 9) % 9 = a n % 9 := by
    intro n hn
    induction' n using Nat.strongRecOn with n ih
    by_cases l: n < 3
    .
      interval_cases n
      .
        simp [a] at hn
        tauto
      .
        simp [a] at hn
        tauto
    .
      replace l: 3 ≤ n := by omega
      clear hn
      rw [show n + 9 = n + 6 + 3 by omega]
      rw [a]
      rw [show n + 6 + 2 = n + 8 by omega]
      rw [show n + 6 + 1 = n + 7 by omega]
      have s1:= ih (n - 1) (by omega) (by omega)
      rw [show n - 1 + 9 = n + 8 by omega] at s1
      have s2:= ih (n - 2) (by omega) (by omega)
      rw [show n - 2 + 9 = n + 7 by omega] at s2
      rw [Nat.mul_mod]
      rw [Nat.add_mod]
      rw [s1, s2]
      nth_rewrite 3 [show n = n - 3 + 3 by omega]
      rw [a]
      rw [show n - 3 + 1 = n - 2 by omega]
      rw [show n - 3 + 2 = n - 1 by omega]
      simp

  -- then we can prove by consider N % 9
  set n:= N - 1
  set m:= n / 9
  set r:= n % 9
  have s: n = 9 * m + r := by
    omega
  have sr: r < 9 := by
    omega
  simp [n] at s
  replace s: N = 9 * m + r + 1 := by
    omega
  rw [s]
  clear_value m r n
  clear s
  induction' m with m ih
  .
    simp
    interval_cases r
    all_goals simp [a, R]
  .
    rw [show 9 * (m + 1) + r + 1 = 9 * m + r + 1 + 9 by omega]
    specialize p (9 * m + r + 1) (by omega)
    rw [p]
    rw [ih]