import Mathlib

/-In the sequence 2001, 2002, 2003, ... , each term after the third is found by
subtracting the previous term from the sum of the two terms that precede that term.
For example, the fourth term is 2001 + 2002 - 2003 = 2000. What is the 2004th term
in this sequence?
(A) - 2004 () - 2 (C) 0 (D) 4003 (E) 6007-/


def f : ℕ → ℤ
| 0 => 2001
| 1 => 2002
| 2 => 2003
| n + 3 => f n + f (n + 1) - f (n + 2)

theorem algebra_95405 : f 2003 = 0 := by 
  set_option maxRecDepth 10000 in 
  norm_num [f]