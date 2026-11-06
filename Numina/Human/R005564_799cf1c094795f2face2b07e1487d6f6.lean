import Mathlib

/- Find the number of integers $x$ such that the following three conditions all hold:

- $x$ is a multiple of 5
- $121<x<1331$
- When $x$ is written as an integer in base 11 with no leading 0s (i.e. no 0s at the very left), its rightmost digit is strictly greater than its leftmost digit. -/
theorem number_theory_608900 :
    Set.ncard {x : ℕ | 5 ∣ x ∧ (121 < x ∧ x < 1331) ∧ (Nat.digits 11 x).head! > (Nat.digits 11 x).getLast!} = 99 := by
  -- We rewrite the set as a `Finset`.
  have H : {x : ℕ | 5 ∣ x ∧ (121 < x ∧ x < 1331) ∧ (Nat.digits 11 x).head! > (Nat.digits 11 x).getLast!} = {x ∈ Finset.Ioo 121 1331 | 5 ∣ x ∧ (Nat.digits 11 x).head! > (Nat.digits 11 x).getLast!} := by
    ext x
    simp
    tauto
  -- We can count the numbers by computing the cardinality of the `Finset`.
  rw [H, Set.ncard_coe_Finset]
  native_decide
