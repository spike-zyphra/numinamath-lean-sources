import Mathlib

/- What is the ones digit of 222,222−22,222−2,222−222−22−2?
(A) 0(B) 2(C) 4(D) 6(E) 8 -/
theorem number_theory_94746 : (222222 - 22222 - 2222 - 222 - 22 - 2) % 10 = 2 := by rfl
--the claim comes from checking the rest of the division mod 10 of the resulting number