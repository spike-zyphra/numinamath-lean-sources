import Mathlib

/-- The base-nine representation of the number N is 27,006,000,052​.
    What is the remainder when NN is divided by 5?
   (A) 0(B) 1(C) 2(D) 3(E) 4(A) -/
theorem number_theory_92976 {N : ℕ} (hN : Nat.digits 9 N = [2,5,0,0,0,0,6,0,0,7,2]) :
    N % 5 = 3 := by
  -- Consider instead the same digits in base 4, which yield the same outcome mod 5 due to 9 = 4 % 5.
  rw[← Nat.ofDigits_digits 9 N, hN, Nat.ofDigits_mod]
  -- A simple computation shows the right result.
  simp[Nat.ofDigits_cons]