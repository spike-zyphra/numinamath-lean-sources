import Mathlib

set_option maxRecDepth 100000

/- Fermat number -/
def f_4617 (n : ℕ) := 2^(2^n) + 1

/- Use the fact that every prime divisor of \( F_{2} = 2^{2^{3}} + 1 \) is of the form \( 2^{7} k + 1 = 128 k + 1 \) to demonstrate that the prime factorization of \( F_{5} \) is \( F_{5} = 641 \cdot 6700417 \).-/
theorem number_theory_4617 (k m: ℕ) (h : f_4617 3 = (128*k+1)*m) :
    Nat.primeFactorsList (f_4617 5)=[641, 6700417] := by
  simp [f_4617]
  unfold Nat.primeFactorsList
  simp
  norm_num
  unfold Nat.primeFactorsList
  simp
  norm_num
