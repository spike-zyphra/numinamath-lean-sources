import Mathlib

theorem number_theory_19510 {n : ℕ} : 5 * n ≡ 8 [MOD 17] ↔ n ≡ 5 [MOD 17] := by
  apply Iff.intro
  · -- Assume 5n ≡ 8 [MOD 17], prove n ≡ 5 [MOD 17]
    intro h
    norm_num [Nat.ModEq] at h ⊢
    omega
  · -- Assume n ≡ 5 [MOD 17], prove 5n ≡ 8 [MOD 17]
    intro h
    norm_num [Nat.ModEq] at h ⊢
    omega