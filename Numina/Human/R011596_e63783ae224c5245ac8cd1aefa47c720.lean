import Mathlib

/- 7.1. The numbers $1,2,3,4,5,6$ were written in some order and denoted by the letters $a, b, c, d, e, f$. Can the equality

$$
(a-1)(b-2)(c-3)(d-4)(e-5)(f-6)=75 ?
$$

# -/
theorem number_theory_289621 :
    ∃ a b c d e f : ℤ, [a, b, c, d, e, f].Perm [1, 2, 3, 4, 5, 6] ∧ (a - 1) * (b - 2) * (c - 3) * (d - 4) * (e - 5) * (f - 6) = 75 := by
  -- Set a = 6, b = 3, c = 4, d = 5, e = 2, f = 1.
  use 6, 3, 4, 5, 2, 1
  -- We can compute it by `native_decide`, which can be done by hand.
  native_decide
