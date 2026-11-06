import Mathlib

theorem number_theory_19510 {n : ℕ} : 5 * n ≡ 8 [MOD 17] ↔ n ≡ 5 [MOD 17] := by
  apply Iff.intro
  . intro h
    norm_num [Nat.ModEq] at h ⊢
    omega
  intro h
  norm_num [Nat.ModEq] at h ⊢
  omega
