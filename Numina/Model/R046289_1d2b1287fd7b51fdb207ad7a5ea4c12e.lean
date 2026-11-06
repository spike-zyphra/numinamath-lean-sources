import Mathlib

theorem algebra_188067 {x y z : ℝ} (h1 : y + z = x * y * z) (h2 : z + x = x * y * z)
    (h3 : x + y = x * y * z) :
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = Real.sqrt 2 ∧ y = Real.sqrt 2 ∧ z = Real.sqrt 2) ∨
    (x = -Real.sqrt 2 ∧ y = -Real.sqrt 2 ∧ z = -Real.sqrt 2) := by

  have h4 : y = x := by
    nlinarith
  -- Prove z = x
  have h5 : z = x := by
    nlinarith [h4]
  -- Substitute variables
  rw [show y = x by linarith [h4], show z = x by linarith [h5]] at h1 h2 h3
  -- Simplify to one equation
  have h7 : x^3 = 2 * x := by
    nlinarith
  -- Factor the equation
  have h8 : x * (x ^ 2 - 2) = 0 := by
    nlinarith
  -- Use cases for factorization
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- Case x = 0
    left
    constructor
    · linarith
    constructor
    · nlinarith
    · nlinarith
  · -- Case x^2 - 2 = 0
    have h11 : x^2 = 2 := by
      nlinarith
    have h12 : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
      have h12 : x^2 = (2 : ℝ) := h11
      have h13 : x^2 - (2 : ℝ) = 0 := by linarith
      have h14 : (x - Real.sqrt 2) * (x + Real.sqrt 2) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      cases' (mul_eq_zero.mp h14) with h15 h16
      · -- Case x - sqrt(2) = 0
        left
        linarith
      · -- Case x + sqrt(2) = 0
        right
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
    cases' h12 with h13 h14
    · -- Case x = sqrt(2)
      right
      left
      constructor
      · linarith [h13]
      constructor
      · nlinarith [h13, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      · nlinarith [h13, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    · -- Case x = -sqrt(2)
      right
      right
      constructor
      · linarith [h14]
      constructor
      · nlinarith [h14, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      · nlinarith [h14, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]