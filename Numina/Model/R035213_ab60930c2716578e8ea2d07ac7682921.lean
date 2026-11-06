import Mathlib

theorem algebra_193518 (a : ℝ) :
    (∃ x y, x^2 + 4 * (y - a)^2 = 4 ∧ x^2 = 2 * y) ↔
    -1 ≤ a ∧ a ≤ 17 / 8 := by
  constructor
  · -- Assume existence, prove bounds 
    rintro ⟨x, y, h₁, h₂⟩
    have h3 : 2 * y + 4 * (y - a)^2 = 4 := by
      have h6 : x^2 = 2 * y := h₂
      rw [h6] at h₁
      linarith
    constructor
    · -- Prove -1 ≤ a
      nlinarith [sq_nonneg (y - (4 * a - 1) / 4), sq_nonneg (x), sq_nonneg (y + 1), sq_nonneg (a + 1), sq_nonneg (a - 17 / 8)]
    · -- Prove a ≤ 17 / 8
      nlinarith [sq_nonneg (y - (4 * a - 1) / 4), sq_nonneg (x), sq_nonneg (y + 1), sq_nonneg (a + 1), sq_nonneg (a - 17 / 8)]
  · -- Assume bounds, prove existence
    rintro ⟨ha1, ha2⟩
    have h4 : 17 - 8 * a ≥ 0 := by
      nlinarith 
    use Real.sqrt ((4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2)
    use (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 4
    constructor
    · -- Substitute and verify first equation
      nlinarith [Real.sqrt_nonneg ((4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2), Real.sq_sqrt (show (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2 ≥ 0 by
        nlinarith [Real.sqrt_nonneg (17 - 8 * a), Real.sq_sqrt (show (17 - 8 * a) ≥ 0 by linarith)]
      ), sq_nonneg (Real.sqrt (17 - 8 * a) - 3), Real.sq_sqrt (show (17 - 8 * a) ≥ 0 by linarith)]
    · -- Substitute and verify second equation
      have h5 : ((4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (17 - 8 * a), Real.sq_sqrt (show (17 - 8 * a) ≥ 0 by linarith)]
      have h5a : Real.sqrt ((4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2) ^ 2 = (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2 := Real.sq_sqrt (by
        nlinarith [Real.sqrt_nonneg (17 - 8 * a), Real.sq_sqrt (show (17 - 8 * a) ≥ 0 by linarith)]
      )
      nlinarith [Real.sqrt_nonneg ((4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2), Real.sq_sqrt (show (4 * a - 1 + Real.sqrt (17 - 8 * a)) / 2 ≥ 0 by
        nlinarith [Real.sqrt_nonneg (17 - 8 * a), Real.sq_sqrt (show (17 - 8 * a) ≥ 0 by linarith)]
      ), h5a]