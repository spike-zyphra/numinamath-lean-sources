import Mathlib

def f : ℕ → ℕ
| 0 => 1
| 1 => 1
| n + 2 => if Even n then f (n / 2) + 1 else f (n / 2)

/- Consider the sequence $1,1,2,1,2,3,1,2,3,4,\cdots$, find the 2020th term of the sequence.

 -/
theorem number_theory_6394 : f 2019 = 4 := by 
  native_decide