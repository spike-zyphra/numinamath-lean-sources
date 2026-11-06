import Mathlib

theorem number_theory_66950 : 
    (∑ k in Finset.Icc 1 1008, k * Nat.choose 2017 k) ≡ 0 [ZMOD 2017^2] ∧
    (∑ k in Finset.Icc 1 504, (-1 : ℤ)^k * Nat.choose 2017 k) ≡ 3 * (2^2016 - 1) [ZMOD 2017^2] := by
  native_decide