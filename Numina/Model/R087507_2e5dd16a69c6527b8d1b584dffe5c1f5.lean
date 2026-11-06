import Mathlib

theorem number_theory_19194 (n : ℕ) (h : 6 * n ≡ 7 [MOD 13]) : n ≡ 12 [MOD 13] := by
  norm_num [Nat.ModEq] at h ⊢
  omega