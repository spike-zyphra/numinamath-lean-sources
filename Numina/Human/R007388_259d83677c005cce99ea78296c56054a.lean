import Mathlib

open Real Set

namespace number_theory_95648

/- R(n) is the sum of elements of the (n + 1)st row -/
def R (n : ℕ) : ℤ := match n with
| 0 => 1
| n + 1 => 2 * R n + (n + 2) - 2

end number_theory_95648

open number_theory_95648

/- Rows 1, 2, 3, 4, and 5 of a triangular array of integers are shown below.
Each row after the first row is formed by placing a 1 at each end of the row, and each interior entry is 1 greater than the sum of the two numbers diagonally above it in the previous row. What is the units digits of the sum of the 2023 numbers in the 2023rd row? -/
theorem number_theory_95648 : R (2023 - 1) % 10 = 5 := by
  -- show that R n = 2 ^ (n + 1) - (n + 1)
  have R_eq n : R n = 2 ^ (n + 1) - (n + 1) := by
    -- proof by induction
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [R, ih]; push_cast
      ring
  rw [R_eq]
  -- finish the proof by computing the last digit of R (2023 - 1)
  norm_num