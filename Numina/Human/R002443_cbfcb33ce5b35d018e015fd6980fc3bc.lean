import Mathlib

/- The sum of the two 5-digit numbers AMC10 and AMC12 is 123422. What is A+M+C?
(A) 10(B) 11(C) 12(D) 13(E) 14 -/
theorem number_theory_94547 (A M C : ℕ) (hA : A < 10) (hM : M < 10) (hC : C < 10)
(h : (A * 10000 + M * 1000 + C * 100 + 10) + (A * 10000 + M * 1000 + C * 10 + 12) = 123422) :
A + M + C = 14 := by
-- The problem is based on solving algebriac step in the hypothesis h
  omega