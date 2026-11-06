import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_144685 (x : ℝ) (hx : 0 < x) :
    (sqrt x - 6) / (2 - sqrt (x + 4)) ≥ 2 + sqrt (x + 4) ↔ x ∈ Ioc 0 4 := by
  have h1 : sqrt (x + 4) > 2 := by
    have h2 : x + 4 > 4 := by
      linarith [hx]
    have h3 : Real.sqrt (x + 4) > Real.sqrt 4 := Real.sqrt_lt_sqrt (by linarith) (by linarith)
    have h4 : Real.sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
    linarith [h4, h3]
  have h2 : (2 - Real.sqrt (x + 4)) < 0 := by
    linarith [h1]

  constructor
  · -- Show that if the inequality holds, then x ∈ Ioc 0 4
    intro h
    have h3 : sqrt x - 6 ≤ (2 + sqrt (x + 4)) * (2 - sqrt (x + 4)) := by
      apply (le_div_iff_of_neg h2).mp at h
      linarith
    have h4 : (2 + sqrt (x + 4)) * (2 - sqrt (x + 4)) = -x := by
      nlinarith [Real.sqrt_nonneg (x + 4), Real.sq_sqrt (show (0 : ℝ) ≤ x + 4 by linarith)]
    have h5 : sqrt x + x ≤ 6 := by
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x + 4), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
    have h7 : x ≤ 4 := by
      nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), sq_nonneg (sqrt x - 2)]
    constructor
    · linarith
    · linarith
  · -- Show that if x ∈ Ioc 0 4, then the inequality holds
    rintro ⟨h0, h4⟩
    have h3 : sqrt x - 6 ≤ (2 + sqrt (x + 4)) * (2 - sqrt (x + 4)) := by
      have h9 : (2 + Real.sqrt (x + 4)) * (2 - Real.sqrt (x + 4)) = -x := by
        nlinarith [Real.sqrt_nonneg (x + 4), Real.sq_sqrt (show (0 : ℝ) ≤ x + 4 by linarith)]
      have h4 : sqrt x ≤ 2 := by
        have h8 : x ≤ 4 := by linarith
        have h5 : Real.sqrt x ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
        have h3 : Real.sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
        linarith [h3, h5]
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x + 4), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)]
    have h5 : (sqrt x - 6) / (2 - Real.sqrt (x + 4)) ≥ 2 + Real.sqrt (x + 4) := by
      apply (le_div_iff_of_neg h2).mpr
      linarith [h3]
    exact h5