import Mathlib

theorem number_theory_23274 (n : ℕ) (h : 3 * n ≡ 2 [MOD 11]) :
    n ≡ 8 [MOD 11] := by
  norm_num [Nat.ModEq] at h ⊢
  omega