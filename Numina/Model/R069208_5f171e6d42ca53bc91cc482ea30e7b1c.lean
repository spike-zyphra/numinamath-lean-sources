import Mathlib

theorem number_theory_203985 (x : ℕ) (h : 5 * x ≡ 11 [MOD 43]) :
    x ≡ 28 [MOD 43] := by
  norm_num [Nat.ModEq] at h ⊢
  omega