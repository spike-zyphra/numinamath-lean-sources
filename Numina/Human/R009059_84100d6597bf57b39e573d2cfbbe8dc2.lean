import Mathlib
import Mathlib.Tactic.NormNum

/--
Consider the statement: "If n is not prime, then (n - 2) is prime."
Which of the following values of `n` is a counterexample to this statement?

(A) 11  
(B) 15  
(C) 19  
(D) 21  
(E) 27
-/

theorem number_theory_93248 : 27 - 2 = 25 ∧ ¬ Nat.Prime 27 ∧ ¬ Nat.Prime 25 := by
    -- 1) First, we see that 27 is not prime.
  have not_prime_27 : ¬ Nat.Prime 27 := by
    -- Since 27=3*9, then 27 is composite, i.e. it is not prime.
    decide
    -- 2) Second, we display that 25 is not prime.
  have not_prime_25 : ¬ Nat.Prime 25 := by
    -- Since 25=5*5, then 25 is not prime.
    decide
    -- 3) Finally, 27-2=25 trivially
  norm_num