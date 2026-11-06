import Mathlib

/-Let $S$ be a positive integer. A natural number $a$ is called "S-lucky" if the sum of its base-10 digits is $S$.
Let $L_i$ denote the $i$-th S-lucky number when all S-lucky numbers are arranged in ascending order (so $L_1 < L_2 < L_3 < \dots$).
Suppose for $S=4$, the S-lucky number $A=40$ is the $n$-th S-lucky number (i.e., $L_n = 40$). Determine the value of $L_{3n}$.
Show the answer is 400.-/

theorem number_theory_634790 (n: ℕ) (h: n = (Finset.filter (fun n => ((Nat.digits 10 n).sum = 4)) (Finset.Icc 1 40)).card):
  3 * n = (Finset.filter (fun n => ((Nat.digits 10 n).sum = 4)) (Finset.Icc 1 400)).card := by

  have v: n = 5 := by
    rw [h]
    native_decide
  clear h
  simp [v]
  native_decide