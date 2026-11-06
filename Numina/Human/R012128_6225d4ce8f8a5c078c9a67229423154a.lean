import Mathlib

/- Find a four-digit number such that the square of the sum of the two-digit numbers formed by its first two digits and its last two digits is exactly equal to this four-digit number. -/
theorem number_theory_626340 : {Nat.ofDigits 10 [d, c, b, a] | (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (_ : 0 < a ∧ a ≤ 9 ∧ b ≤ 9 ∧ 0 < c ∧ c ≤ 9 ∧ d ≤ 9) (_ : (Nat.ofDigits 10 [b, a] + Nat.ofDigits 10 [d, c]) ^ 2 = Nat.ofDigits 10 [d, c, b, a])} = {2025, 3025} := by
  ext x
  simp
  constructor
  swap
  -- We first check that 2025 and 3025 are solutions.
  . rintro (rfl | rfl)
    . use 2, 0, 2, 5
      norm_num [Nat.ofDigits]
    . use 3, 0, 2, 5
      norm_num [Nat.ofDigits]
  . -- We rewrite a ∈ Finset.Ioc 0 9, c ∈ Finset.Ioc 0 9, b ∈ Finset.Icc 0 9, d ∈ Finset.Icc 0 9.
    rintro ⟨a, b, c, d, h, ⟨ha₁, ha₂, hb, hc₁, hc₂, hd⟩, rfl⟩
    have ha : a ∈ Finset.Ioc 0 9 := by simp [ha₁, ha₂]
    have hc : c ∈ Finset.Ioc 0 9 := by simp [hc₁, hc₂]
    replace hb : b ∈ Finset.Icc 0 9 := by simp [hb]
    replace hd : d ∈ Finset.Icc 0 9 := by simp [hd]
    -- We revert the assumptions to quantify over a, b, c, d.
    clear ha₁ ha₂ hc₁ hc₂
    revert h
    revert d
    revert c
    revert b
    revert a
    -- We check every case by `native_decide`.
    native_decide
