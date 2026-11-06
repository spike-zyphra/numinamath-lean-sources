import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_211051 (a : ℝ) :
  {x | x^2 - 3 * x + 2 ≤ 0} ⊆ {x | 1 / (x - 3) < a} ↔ a > -1 / 2 := by
  constructor
  · -- Assume {x | x^2 - 3 * x + 2 ≤ 0} ⊆ {x | 1 / (x - 3) < a}, prove a > -1 / 2
    intro h
    have h1 : (1 : ℝ) ^ 2 - 3 * (1 : ℝ) + 2 ≤ 0 := by norm_num
    have h2 : (1 : ℝ) ∈ {x | 1 / (x - 3) < a} := by
      apply h
      norm_num
    simp at h2
    norm_num at h2 ⊢
    linarith
  · -- Assume a > -1 / 2, prove {x | x^2 - 3 * x + 2 ≤ 0} ⊆ {x | 1 / (x - 3) < a}
    intro ha x hx
    have h3 : x ^ 2 - 3 * x + 2 ≤ 0 := by
      simpa using hx
    have h4 : 1 ≤ x := by nlinarith
    have h5 : x ≤ 2 := by nlinarith
    have h6 : x - 3 < 0 := by nlinarith
    have h7 : 1 / (x - 3) ≤ -1 / 2 := by
      apply (div_le_iff_of_neg' (by nlinarith)).mpr
      nlinarith
      all_goals linarith
    have h8 : (1 / (x - 3) : ℝ) < a := by
      have h9 : (1 / (x - 3) : ℝ) ≤ -1 / 2 := h7
      have h10 : -1 / 2 < a := by linarith
      linarith
    simpa using h8