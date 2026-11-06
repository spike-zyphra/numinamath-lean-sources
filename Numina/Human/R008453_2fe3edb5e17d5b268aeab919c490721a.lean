import Mathlib

def dig_change : ℕ → ℕ 
| 0 => 0
| 1 => 1
| 2 => 3
| 3 => 4
| 4 => 5
| 5 => 6
| 6 => 7
| 7 => 8
| 8 => 9
| (n + 1) => 0

 
/- Johnny the grad student is typing all the integers from 1 to $\infty$, in order. The 2 on his computer is broken however, so he just skips any number with a 2 . What's the 2008th number he types?-/
theorem number_theory_608445 : List.map dig_change (Nat.digits 9 2008) = [1, 8, 7 ,3] := by 
  -- first express 2008 in 9-adic, then use the digit change map in the digit list
  have eq_aux : (Nat.digits 9 2008) = [1, 7, 6, 2] := by 
    norm_num
  rw [eq_aux]
  unfold dig_change
  simp