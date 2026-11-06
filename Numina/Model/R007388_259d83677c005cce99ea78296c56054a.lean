import Mathlib

open Real Set

namespace number_theory_95648

/- R(n) is the sum of elements of the (n + 1)st row -/
def R (n : ℕ) : ℤ := match n with
| 0 => 1
| n + 1 => 2 * R n + (n + 2) - 2

end number_theory_95648

open number_theory_95648

theorem number_theory_95648 : R (2023 - 1) % 10 = 5 := by
  native_decide