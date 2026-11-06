import Mathlib

/- 90. There is a sequence of numbers: $1,1,2,3,5,8,13,21,34,55,89, \cdots \cdots$ Starting from the third number, each number is the sum of the two preceding ones. Then, the remainder when the 2007th number in this sequence is divided by 7 is -/
theorem number_theory_222856 : Nat.fib 2007 % 7 = 6 := by
  -- show that the Fibonacci sequence has period 16 when taken mod 7
  have h1 : ∀ n, Nat.fib (n + 16) % 7 = Nat.fib n % 7
  · intro n
    induction' n using Nat.strong_induction_on with n ih
    match n with
    | 0 => norm_num
    | 1 => norm_num
    | m + 2 =>
      rw [show m + 2 + 16 = m + 16 + 2 by ring, Nat.fib_add_two, Nat.add_mod,
          ih m (by linarith), show m + 16 + 1 = m + 1 + 16 by ring,
          ih (m + 1) (by linarith), Nat.fib_add_two, ←Nat.add_mod]
  -- show that the 7th value is 6
  have h2 : ∀ n, Nat.fib (16 * n + 7) % 7 = 6
  · intro n
    induction n with
    | zero => norm_num
    | succ n ih => rw [show 16 * (n + 1) + 7 = 16 * n + 7 + 16 by ring, h1, ih]
  -- show that this is the value we want
  rw [show 2007 = 16 * 125 + 7 by norm_num, h2]