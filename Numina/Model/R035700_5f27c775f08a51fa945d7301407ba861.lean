import Mathlib

theorem algebra_126660 : ∃ a b c : ℕ, a > 0 ∧ a ≤ 2019 ∧ b ≤ 2019 ∧ c ≤ 2019 ∧ ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ a * x1 ^ 2 + b * x1 + c = 0 ∧ a * x2 ^ 2 + b * x2 + c = 0 ∧ |x1 - x2| < 0.01 := by
  use 1600, 81, 1
  constructor
  · -- show that a > 0
    norm_num
  constructor
  · -- show that a ≤ 2019
    norm_num
  constructor
  · -- show that b ≤ 2019
    norm_num
  constructor
  · -- show that c ≤ 2019
    norm_num
  · -- show the existence of two real roots
    use (-81 + Real.sqrt 161) / 3200, (-81 - Real.sqrt 161) / 3200
    constructor
    · -- show that x1 ≠ x2
      by_contra h
      have h1 : (-81 + Real.sqrt 161 : ℝ) / 3200 = (-81 - Real.sqrt 161 : ℝ) / 3200 := by linarith [h]
      have h2 : (-81 + Real.sqrt 161 : ℝ) = (-81 - Real.sqrt 161 : ℝ) := by linarith [h1]
      have h3 : Real.sqrt 161 = 0 := by linarith [h2]
      have h4 : Real.sqrt 161 > 0 := by
        positivity
      linarith [h3, h4]
    constructor
    · -- show that x1 is a root
      field_simp
      ring_nf
      rw [Real.sq_sqrt]
      all_goals norm_num
    constructor
    · -- show that x2 is a root
      field_simp
      ring_nf
      rw [Real.sq_sqrt]
      all_goals norm_num
    · -- show that |x1 - x2| < 0.01
      have h1 : ((-81 + Real.sqrt 161) / 3200 : ℝ) - ((-81 - Real.sqrt 161) / 3200 : ℝ) = (2 * Real.sqrt 161) / 3200 := by ring
      rw [show |(((-81 + Real.sqrt 161) / 3200 : ℝ) - ((-81 - Real.sqrt 161) / 3200 : ℝ))| = |(2 * Real.sqrt 161 / 3200 : ℝ)| by rw [h1]]
      have h3 : |(2 * Real.sqrt 161 / 3200 : ℝ)| = (Real.sqrt 161 / 1600 : ℝ) := by
        have h4 : (2 * Real.sqrt 161 / 3200 : ℝ) = (Real.sqrt 161 / 1600 : ℝ) := by ring
        rw [h4]
        have h5 : 0 ≤ (Real.sqrt 161 / 1600 : ℝ) := by
          have h6 : 0 ≤ Real.sqrt 161 := by positivity
          have h7 : (0 : ℝ) ≤ (1600 : ℝ) := by norm_num
          apply div_nonneg
          exact h6
          all_goals norm_num
        rw [abs_of_nonneg h5]
      rw [h3]
      have h4 : Real.sqrt 161 < (16 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 161, Real.sq_sqrt (show (0 : ℝ) ≤ (161 : ℝ) by norm_num)]
      have h5 : (Real.sqrt 161 / 1600 : ℝ) < (0.01 : ℝ) := by
        norm_num at h4 ⊢
        nlinarith [Real.sqrt_nonneg 161, Real.sq_sqrt (show (0 : ℝ) ≤ (161 : ℝ) by norm_num)]
      linarith [h5]