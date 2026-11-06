import Mathlib

theorem inequalities_34387 (a : ℝ) :
    ∃ x y z : ℝ, 3*x^2+2*y^2+2*z^2=a ∧ 4*x^2+4*y^2+5*z^2=1-a ↔
    2/7 ≤ a ∧ a ≤ 3/7 := by

  use (Real.sqrt (a - 2/7)), (0), (Real.sqrt ((3 - 7*a)/7))

  constructor
  · -- If the equations hold, then 2/7 ≤ a ≤ 3/7
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : 0 ≤ (Real.sqrt (a - 2/7) : ℝ) ^ 2 := by
      apply sq_nonneg
    have h4 : (Real.sqrt (a - 2/7) : ℝ) ^ 2 = a - 2/7 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h5 : 0 ≤ (Real.sqrt ((3 - 7*a)/7) : ℝ) ^ 2 := by
      apply sq_nonneg
    have h6 : (Real.sqrt ((3 - 7*a)/7) : ℝ) ^ 2 = (3 - 7*a)/7 := by
      rw [Real.sq_sqrt]
      nlinarith
    constructor
    · -- Show 2/7 ≤ a
      nlinarith [h4]
    · -- Show a ≤ 3/7
      nlinarith [h6]
  · -- If 2/7 ≤ a ≤ 3/7, then the equations hold
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : 0 ≤ (a - 2/7 : ℝ) := by linarith
    have h4 : 0 ≤ ( (3 - 7*a)/7 : ℝ ) := by nlinarith
    have h5 : (Real.sqrt (a - 2/7) : ℝ) ^ 2 = a - 2/7 := by
      rw [Real.sq_sqrt]
      linarith
    have h6 : (Real.sqrt ((3 - 7*a)/7) : ℝ) ^ 2 = (3 - 7*a)/7 := by
      rw [Real.sq_sqrt]
      nlinarith
    constructor
    · -- Show 3*x^2 + 2*y^2 + 2*z^2 = a
      nlinarith [h5, h6]
    · -- Show 4*x^2 + 4*y^2 + 5*z^2 = 1 - a
      nlinarith [h5, h6]