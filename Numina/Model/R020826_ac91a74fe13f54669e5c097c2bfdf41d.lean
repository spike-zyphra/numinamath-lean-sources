import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_171007 (x : ℝ) : 216 * x^6 + 19 * x^3 < 1 ↔
    x ∈ Ioo (-1/2) (1/3) := by
  simp only [mem_Ioo]
  constructor
  · -- Assume 216 * x^6 + 19 * x^3 < 1, prove -1/2 < x < 1/3
    intro h
    have h1 : -1/8 < x^3 := by 
      nlinarith [sq_nonneg (x^3 - 1/27), sq_nonneg (x^3 + 1/8), sq_nonneg (x^2 - 1/4), sq_nonneg (x^2 - 1/9), sq_nonneg (x^2 * x^3)]
    have h2 : x^3 < 1/27 := by 
      nlinarith [sq_nonneg (x^3 - 1/27), sq_nonneg (x^3 + 1/8), sq_nonneg (x^2 - 1/4), sq_nonneg (x^2 - 1/9), sq_nonneg (x^2 * x^3)]
    constructor
    · -- Prove -1/2 < x
      nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 3), sq_nonneg (x^2 ), sq_nonneg ((x + 1 / 2) * (x - 1 / 3)), sq_nonneg ((x^3 + 1 / 8) ), sq_nonneg ((x^3 - 1 / 27) ) ]
    · -- Prove x < 1/3
      nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (x + 1 / 2), sq_nonneg (x^2 ), sq_nonneg ((x + 1 / 2) * (x - 1 / 3)), sq_nonneg ((x^3 + 1 / 8) ), sq_nonneg ((x^3 - 1 / 27) ) ]
  · -- Assume -1/2 < x < 1/3, prove 216 * x^6 + 19 * x^3 < 1
    rintro ⟨h1, h2⟩
    have h3 : -1 / 8 < x ^ 3 := by
      nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 3), sq_nonneg (x^2 ), sq_nonneg ((x + 1 / 2) * (x - 1 / 3))]
    have h4 : x ^ 3 < 1 / 27 := by
      nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (x - 1 / 3), sq_nonneg (x^2 ), sq_nonneg ((x + 1 / 2) * (x - 1 / 3))]
    nlinarith [sq_nonneg (x^3 - 1 / 27), sq_nonneg (x^3 + 1 / 8), sq_nonneg (x^2 - 1 / 4), sq_nonneg (x^2 - 1 / 9), sq_nonneg (x^2 * x^3), sq_nonneg ((x + 1 / 2) * (x - 1 / 3) ) ]