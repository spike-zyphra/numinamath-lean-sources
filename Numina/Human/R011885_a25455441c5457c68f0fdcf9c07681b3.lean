import Mathlib

open Finset

/- 4. In the number $2016 * * * * 02 *$, each of the 5 asterisks needs to be replaced with any of the digits $0,2,4,5,7,9$ (digits can be repeated) so that the resulting 11-digit number is divisible by 15. In how many ways can this be done? -/
theorem number_theory_162979 (S : Finset ℕ) (hS : S = {0, 2, 4, 5, 7, 9}) :
    #((S ×ˢ S ×ˢ S ×ˢ S ×ˢ S).filter (fun (a, b, c, d, e) => 15 ∣ Nat.ofDigits 10 [e, 2, 0, d, c, b, a, 6, 1, 0, 2])) = 864 := by
  -- Note on the formalization:
  -- Let (a, b, c, d, e) be the five asterisks from left to right.
  -- Then the number of ways to replace the asterisks is the cardinality of the set
  -- {(a, b, c, d, e) ∈ S ×ˢ S ×ˢ S ×ˢ S ×ˢ S | 15 ∣ Nat.ofDigits 10 [e, 2, 0, d, c, b, a, 6, 1, 0, 2]}.
  rw [hS]
  -- We can use `native_decide` to check all cases.
  native_decide
