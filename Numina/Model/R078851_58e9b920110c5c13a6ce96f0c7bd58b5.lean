import Mathlib

theorem number_theory_166849 :
    (∑ n in Finset.Icc 1 235, (Nat.digits 10 n).count 4) = 44 ∧
    (∑ n in Finset.Icc 1 235, (Nat.digits 10 n).count 0) = 43 ∧
    (∑ n in Finset.Icc 1 235, (Nat.digits 10 n).length) = 597 := by
  constructor
  · -- Proof of the first part: counting digit 4
    native_decide
  constructor
  · -- Proof of the second part: counting digit 0
    native_decide
  · -- Proof of the third part: total digits
    native_decide