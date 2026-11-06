import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_15897 :
  IsLeast {t : ℝ | ∃ x y, x ∈ Icc (2/5) (1/2) ∧ y ∈ Icc (1/3) (3/8) ∧ t = x * y / (x ^ 2 + y ^ 2)} (6/13) := by
  constructor
  · -- Show 6/13 is in the set.
    use 1 / 2, 1 / 3
    constructor
    · norm_num [mem_Icc]
    constructor
    · norm_num [mem_Icc]
    · norm_num
  · -- Show 6/13 is the least element in the set.
    intro t ht
    rcases ht with ⟨x, y, hx, hy, ht⟩
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    have h1 : x * y / (x ^ 2 + y ^ 2) ≥ 6 / 13 := by
      have h2 : x ^ 2 + y ^ 2 > 0 := by
        nlinarith [show (2/5 : ℝ) > 0 by norm_num, show (1/3 : ℝ) > 0 by norm_num, hx1, hy1, hx2, hy2]
      have h3 : x * y ≥ (6 / 13) * (x ^ 2 + y ^ 2) := by
        nlinarith [show (2/5 : ℝ) ≤ x by linarith, show x ≤ (1/2 : ℝ) by linarith, show (1/3 : ℝ) ≤ y by linarith, show y ≤ (3/8 : ℝ) by linarith, mul_nonneg (show (0 : ℝ) ≤ x - 2/5 by nlinarith) (show (0 : ℝ) ≤ 1/2 - x by nlinarith), mul_nonneg (show (0 : ℝ) ≤ y - 1/3 by nlinarith) (show (0 : ℝ) ≤ 3/8 - y by nlinarith)]
      have h4 : x * y / (x ^ 2 + y ^ 2) ≥ (6 / 13) := by
        have h5 : x^2 + y^2 > 0 := h2
        apply (le_div_iff₀ (by linarith)).mpr
        linarith
      linarith
    linarith [ht, h1]