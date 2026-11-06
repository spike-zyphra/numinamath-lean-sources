import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_143914 (x : ℝ) :
  5 - x^2 ≥ 0 ↔ x ∈ Icc (-sqrt 5) (sqrt 5) := by
  constructor
  · -- Assume $5 - x^2 \geq 0$, prove $x \in \[-\sqrt{5}, \sqrt{5}\]$
    intro h
    have h1 : x^2 ≤ 5 := by linarith
    have h2 : -sqrt 5 ≤ x := by
      have h8 : (sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)
      nlinarith [Real.sqrt_nonneg 5, h1, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
    have h4 : x ≤ sqrt 5 := by
      have h5 : sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
      have h6 : x^2 ≤ (sqrt 5) ^ 2 := by
        have h7 : (sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)
        linarith [h1, h7]
      nlinarith [Real.sqrt_nonneg 5]
    exact ⟨h2, h4⟩
  · -- Assume $x \in \[-\sqrt{5}, \sqrt{5}\]$, prove $5 - x^2 \geq 0$
    rintro ⟨h1, h2⟩
    have h3 : x^2 ≤ (sqrt 5) ^ 2 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
    have h4 : (sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)
    linarith [h3, h4]