import Mathlib

/- g(n) = 2^(4n+2) + 1 -/
def g_4612 (n : ℕ) := 2^(4*n+2) + 1

theorem formal_2854 (x n m : ℕ) (h : 2^(4*n+2) = (4 * x^4 + 1) * m) :
    Nat.primeFactorsList (g_4612 4)=[5,13,37,109] := by 
  native_decide