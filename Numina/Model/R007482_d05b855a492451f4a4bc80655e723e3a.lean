import Mathlib

theorem number_theory_115152 : (∏ i ∈ Finset.range 2015, (i + 1)) + 4051 ≡ 23 [ZMOD 4 * (5^3 + 3 * 5^3) + 3^2 + 5] ∧ (∀n, n ≡ 6 [MOD 8] → n ≡ 4 [MOD 10] → n ≡ 14 [MOD 40]) := by
  constructor
  · -- First part: prove the modular equivalence
    native_decide
  · -- Second part: prove the remainder when n is divided by 40
    intro n hn1 hn2
    norm_num [Nat.ModEq] at hn1 hn2 ⊢
    omega