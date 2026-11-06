import Mathlib

/- Find a positive integrer number $n$ such that, if yor put a number $2$ on the left and a number $1$ on the right, the new number is equal to $33n$. -/
theorem number_theory_69875 {n : ℕ} (hn : n = 87) : Nat.ofDigits 10 ([1] ++ Nat.digits 10 n ++ [2]) = 33 * n := by 
  rw [hn]
  native_decide
