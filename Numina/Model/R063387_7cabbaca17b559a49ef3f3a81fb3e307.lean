import Mathlib

theorem number_theory_13709 (x : ℕ) (hx : x > 0) :
    (5 * x ≡ 1 [MOD 7]) ∧ (2 * x ≡ 7 [MOD 11]) ↔ x ≡ 31 [MOD 77] := by
  apply Iff.intro
  · -- Assume (5 * x ≡ 1 [MOD 7]) ∧ (2 * x ≡ 7 [MOD 11]), prove x ≡ 31 [MOD 77]
    intro h
    rcases h with ⟨h1, h2⟩
    norm_num [Nat.ModEq] at h1 h2 ⊢
    omega
  · -- Assume x ≡ 31 [MOD 77], prove (5 * x ≡ 1 [MOD 7]) ∧ (2 * x ≡ 7 [MOD 11])
    intro h
    norm_num [Nat.ModEq] at h ⊢
    constructor
    · -- Verify 5x ≡ 1 [MOD 7]
      omega
    · -- Verify 2x ≡ 7 [MOD 11]
      omega