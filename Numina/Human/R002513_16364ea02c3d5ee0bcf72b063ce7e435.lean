import Mathlib.Data.Nat.Digits

/-- The number which the question is about: The arithmetic mean of the nine numbers
9, 99, ..., 999999999 -/
def M :=
  (∑ x ∈ ({9, 99, 999, 9999, 99999, 999999, 9999999, 99999999, 999999999} : Finset ℚ), x) / 9

/-- The [arithmetic mean](https://artofproblemsolving.com/wiki/index.php/Arithmetic_mean)
of the nine numbers in the set $\{9, 99, 999, 9999, \ldots, 999999999\}$ is a
$9$-digit number $M$, all of whose digits are distinct. The number $M$ doesn't
contain the digit
$\mathrm{(A)}\ 0 \qquad\mathrm{(B)}\ 2 \qquad\mathrm{(C)}\ 4
\qquad\mathrm{(D)}\ 6 \qquad\mathrm{(E)}\ 8$ -/
theorem number_theory_1124 :
    M.isInt ∧
    (Nat.digits 10 M.num.toNat).length = 9 ∧
    (Nat.digits 10 M.num.toNat).Nodup ∧
    0 ∉ (Nat.digits 10 M.num.toNat) := by

  -- Compute the mean of the numbers.
  have hM : M = 123456789 := by
    simp [M]
    norm_num

  -- It can be easily seen that this number has all the required properties.
  simp [hM, Rat.isInt]