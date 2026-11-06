import Mathlib

theorem number_theory_150128 : ¬(27 ∣ (9918 : ℕ)) ∧ (Nat.digits 10 9918).sum ≡ 0 [MOD 27] := by
  constructor
  · -- Show that 9918 is not divisible by 27
    norm_num
  · -- verify that the sum of the digits of 9918 is divisible by 27.
    norm_num [Nat.ModEq]