import Mathlib

/- In multiplying two positive integers a and b,
Ron reversed the digits of the two-digit number a.
His erroneous product was 161. What is the correct value of the product of a and b?
(A) 116(B) 161(C) 204(D) 214(E) 224 -/
theorem number_theory_93358 (a b : ℕ) (ha : a > 0) (hb : b > 0)
(h : a * b = 161) (h' : Nat.ofDigits 10 [a, b] * Nat.ofDigits 10 [b, a] = 161) :
a * b = 224 := by
simp_all [Nat.ofDigits] 
-- Here we are simplifying the hypothesis
nlinarith  
-- we do a calculation to solve the non-linear equations
/- Hence we get the correct product is 224
-/