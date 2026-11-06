import Mathlib

def f (n : ℕ) := n^4 + n^3 + n^2 + n + 1

theorem algebra_296648 : (f (2^5)) % (f 2) = 5 := by
  unfold f
  norm_num