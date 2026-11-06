import Mathlib

theorem algebra_121847 (m : ℝ) :
    (∃ x1 x2 : ℝ, x1 > -2 ∧ x2 > -2 ∧ x1^2 + (2 * m + 6) * x1 + 4 * m + 12 = 0 ∧
      x2^2 + (2 * m + 6) * x2 + 4 * m + 12 = 0) ↔ m ≤ -3 := by
  constructor
  · -- Assume there are two roots greater than -2, then m ≤ -3
    rintro ⟨x1, x2, hx1, hx2, h1, h2⟩
    have h3 : (2 * m + 6)^2 - 4 * (4 * m + 12) ≥ 0 := by
      nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 + (m + 3)), sq_nonneg (x2 + (m + 3)), 
          h1, h2]
    have h4 : m ^ 2 + 2 * m - 3 ≥ 0 := by
      nlinarith
    have h5 : (m + 3) * (m - 1) ≥ 0 := by nlinarith
    nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 + 2), sq_nonneg (x2 + 2),
      h1, h2, h3, h4, h5]
  · -- Assume m ≤ -3, then there are two real roots greater than -2
    intro hm
    have h4 : m ≤ -3 := hm
    have h5 : m ^ 2 + 2 * m - 3 ≥ 0 := by nlinarith
    use -m - 3 + Real.sqrt (m ^ 2 + 2 * m - 3), -m - 3 - Real.sqrt (m ^ 2 + 2 * m - 3)
    constructor
    · -- Show that x1 > -2
      nlinarith [Real.sqrt_nonneg (m ^ 2 + 2 * m - 3), Real.sq_sqrt (show 0 ≤ m ^ 2 + 2 * m - 3 by nlinarith)]
    constructor
    · -- Show that x2 > -2
      nlinarith [Real.sqrt_nonneg (m ^ 2 + 2 * m - 3), Real.sq_sqrt (show 0 ≤ m ^ 2 + 2 * m - 3 by nlinarith)]
    constructor
    · -- Show that x1 is a root
      nlinarith [Real.sqrt_nonneg (m ^ 2 + 2 * m - 3), Real.sq_sqrt (show 0 ≤ m ^ 2 + 2 * m - 3 by nlinarith)]
    · -- Show that x2 is a root
      nlinarith [Real.sqrt_nonneg (m ^ 2 + 2 * m - 3), Real.sq_sqrt (show 0 ≤ m ^ 2 + 2 * m - 3 by nlinarith)]