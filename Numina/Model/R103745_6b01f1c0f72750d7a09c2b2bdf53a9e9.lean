import Mathlib

theorem number_theory_3844 : (13 ≡ 1 [MOD 4]) ∧ ∀ x, 13 ≡ x [MOD 4] → x ≡ 1 [MOD 4] := by
  constructor
  · -- Show 13 ≡ 1 [MOD 4]
    norm_num [Nat.ModEq]
  · intro x h
    norm_num [Nat.ModEq] at h ⊢
    omega