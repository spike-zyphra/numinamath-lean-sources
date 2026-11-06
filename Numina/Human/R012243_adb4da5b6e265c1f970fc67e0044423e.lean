import Mathlib

/- The ratio 2^2001*3^2003/6^2002​ is:
(A) 1/6(B) 1/3(C) 1/2(D) 2/3(E) 3/2(A) 1/6(B) 1/3(C) 1/2(D) 2/3(E) 3/2 -/
theorem algebra_94239 : (2^2001 * 3^2003) / 6^2002 = 3 / 2 := by
  -- This can be evaluated directly using norm_num. To show the details, we proceed by factoring out and then cancelling
  -- 2^2001 * 3^2001 and 6^2001, which leaves us with 9 / 6 = 3 / 2.
  calc (2^2001 * 3^2003) / 6^2002 = (2^2001 * (3^2001 * 3 ^ 2)) / (6 ^ 2001 * 6 ^ 1) := by rw [←Nat.pow_add,←Nat.pow_add]
                                _ = (2^2001*3^2001*3^2)/(6^2001*6) := by rw [Nat.pow_one,Nat.mul_assoc]
                                _ = 3 ^ 2 / 6 := by rw [←Nat.mul_pow]; norm_num
                                _ = 3 / 2 := by norm_num