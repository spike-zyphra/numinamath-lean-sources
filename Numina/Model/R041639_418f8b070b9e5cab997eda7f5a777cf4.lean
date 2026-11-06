import Mathlib

theorem algebra_292365 (a : ℝ) :
    ∃ x y, x^2 + 4 * (y - a)^2 = 4 ∧ x^2 = 2 * y ↔ a ∈ Set.Icc (-1) (17 / 8) := by
  use Real.sqrt (2 * ((4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4))
  use (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4
  constructor
  · -- Forward implication: if (x,y) satisfy both equations, then a ∈ [-1, 17/8]
    rintro ⟨h1, h2⟩
    constructor
    · -- Show that -1 ≤ a
      have h37 : Real.sqrt (17 - 8 * a) ≥ 0 := Real.sqrt_nonneg (17 - 8 * a)
      have h64 : (Real.sqrt (17 - 8 * a) ) ^ 2 = (17 - 8 * a) := Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by
        nlinarith [sq_nonneg ( ( (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4 ) ) ]
      )
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by
        nlinarith [sq_nonneg ( ( (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4 ) ) ]
      ) ]
    · -- Show that a ≤ 17/8
      have h34 : a ≤ 17 / 8 := by
        have h37 : Real.sqrt (17 - 8 * a) ≥ 0 := Real.sqrt_nonneg (17 - 8 * a)
        have h64 : (Real.sqrt (17 - 8 * a) ) ^ 2 = (17 - 8 * a) := Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by
          nlinarith [sq_nonneg ( ( (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4 ) ) ]
        )
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by
          nlinarith [sq_nonneg ( ( (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4 ) ) ]
        ) ]
      linarith
  · -- Backward implication: if a ∈ [-1, 17/8], then (x,y) satisfy both equations.
    rintro ⟨ha1, ha2⟩
    constructor
    · -- Show that x^2 + 4 * (y - a)^2 = 4
      have h34 : Real.sqrt (17 - 8 * a) ≥ 0 := Real.sqrt_nonneg (17 - 8 * a)
      have h64 : (Real.sqrt (17 - 8 * a) ) ^ 2 = (17 - 8 * a) := Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by
        nlinarith
      )
      have h41 : ((4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4 ) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (17 - 8 * a), Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by
          nlinarith
        ) ]
      have h37 : Real.sqrt (2 * ((4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4)) ^ 2 = 2 * ((4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4) := by
        rw [Real.sq_sqrt]
        nlinarith
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (17 - 8 * a : ℝ) by
        nlinarith
      ), h37 ]
    · -- Show that x^2 = 2 * y
      have h34 : Real.sqrt (17 - 8 * a) ≥ 0 := Real.sqrt_nonneg (17 - 8 * a)
      have h41 : ((4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4 ) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (17 - 8 * a), Real.sq_sqrt (show (0 : ℝ) ≤ 17 - 8 * a by
          nlinarith
        ) ]
      have h37 : Real.sqrt (2 * ((4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4)) ^ 2 = 2 * ((4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4) := by
        rw [Real.sq_sqrt]
        nlinarith
      nlinarith [h37]