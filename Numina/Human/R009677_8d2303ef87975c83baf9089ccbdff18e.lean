import Mathlib

/- g(n) = 2^(4n+2) + 1 -/
def g_4612 (n : ℕ) := 2^(4*n+2) + 1

/- Show that any number of the form \(2^{4n+2}+1\) can be easily factored by using the identity \(4x^{4}+1=\left(2x^{2}+2x+1\right)\left(2x^{2}-2x+1\right)\). Factor \(2^{18}+1\) using this identity.-/
theorem formal_2854 (x n m : ℕ) (h : 2^(4*n+2) = (4 * x^4 + 1) * m) :
    Nat.primeFactorsList (g_4612 4)=[5,13,37,109] := by
  -- verify by computation
  simp [g_4612]
  unfold Nat.primeFactorsList
  simp
  norm_num
  unfold Nat.primeFactorsList
  simp
  norm_num
  unfold Nat.primeFactorsList
  simp
  norm_num
  unfold Nat.primeFactorsList
  simp
  norm_num
