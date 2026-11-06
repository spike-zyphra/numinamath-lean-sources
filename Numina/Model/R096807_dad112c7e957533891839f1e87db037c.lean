import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_255167 (a b c : ℝ) (ha : ∀ x ∈ Icc 0 1, |a * x^2 + b * x + c| ≤ 1) :
    |a| + |b| + |c| ≤ 17 := by
  have h1 := ha 0 (left_mem_Icc.mpr (by norm_num))
  have h2 := ha 1 (right_mem_Icc.mpr (by norm_num))
  have h3 := ha (1 / 2) (by norm_num [mem_Icc])
  cases' abs_le.mp h1 with h11 h12
  cases' abs_le.mp h2 with h21 h22
  cases' abs_le.mp h3 with h31 h32
  cases' abs_cases a with ha1 ha1
  · cases' abs_cases b with hb1 hb1
    · cases' abs_cases c with hc1 hc1
      · -- a ≥ 0, b ≥ 0, c ≥ 0
        linarith
      · -- a ≥ 0, b ≥ 0, c ≤ 0
        linarith
    · cases' abs_cases c with hc1 hc1
      · -- a ≥ 0, b ≤ 0, c ≥ 0
        linarith
      · -- a ≥ 0, b ≤ 0, c ≤ 0
        linarith
  · cases' abs_cases b with hb1 hb1
    · cases' abs_cases c with hc1 hc1
      · -- a ≤ 0, b ≥ 0, c ≥ 0
        linarith
      · -- a ≤ 0, b ≥ 0, c ≤ 0
        linarith
    · cases' abs_cases c with hc1 hc1
      · -- a ≤ 0, b ≤ 0, c ≥ 0
        linarith
      · -- a ≤ 0, b ≤ 0, c ≤ 0
        linarith