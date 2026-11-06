import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_276910 (b : ℝ) :
  (∀ m : ℝ, ∃ x y, x^2 + 2 * y^2 = 3 ∧ y = m * x + b) ↔
  b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2) := by
  constructor
  · -- (∀ m : ℝ, ∃ x y, x^2 + 2 * y^2 = 3 ∧ y = m * x + b) → b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2) 
    intro h
    have h1 := h 0
    rcases h1 with ⟨x, y, h_eq1, h_eq2⟩
    have h_eq3 : y = b := by
      nlinarith
    rw [h_eq3] at h_eq1
    have h1 : b ^ 2 ≤ (3 / 2 : ℝ) := by
      nlinarith [sq_nonneg x]
    have h3 : b ≤ sqrt 6 / 2 := by
      have h7 : sqrt 6 ≥ 0 := Real.sqrt_nonneg 6
      have h8 : sqrt 6 / 2 ≥ 0 := by nlinarith
      have h9 : b ^ 2 ≤ (sqrt 6 / 2) ^ 2 := by
        have h10 : (sqrt 6 / 2 : ℝ) ^ 2 = 3 / 2 := by
          nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
        nlinarith [h1, h10]
      nlinarith [Real.sqrt_nonneg 6, sq_nonneg (b - sqrt 6 / 2)]
    have h5 : -sqrt 6 / 2 ≤ b := by
      have h7 : sqrt 6 ≥ 0 := Real.sqrt_nonneg 6
      have h8 : sqrt 6 / 2 ≥ 0 := by nlinarith
      have h9 : b ^ 2 ≤ (sqrt 6 / 2) ^ 2 := by
        have h10 : (sqrt 6 / 2 : ℝ) ^ 2 = 3 / 2 := by
          nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
        nlinarith [h1, h10]
      nlinarith [Real.sqrt_nonneg 6, sq_nonneg (b - (- sqrt 6 / 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    constructor <;> nlinarith
  · -- b ∈ Icc (-sqrt 6 / 2) (sqrt 6 / 2) → (∀ m : ℝ, ∃ x y, x^2 + 2 * y^2 = 3 ∧ y = m * x + b)
    rintro ⟨hb1, hb2⟩
    intro m
    have h1 : b ^ 2 ≤ (3 / 2 : ℝ) := by
      have h2 : (sqrt 6 / 2) ^ 2 = (3 / 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      nlinarith [sq_nonneg (b ^ 2), Real.sqrt_nonneg 6, sq_nonneg (b - sqrt 6 / 2), sq_nonneg (b + sqrt 6 / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    have h2 : (24 * m ^ 2 + 12 - 8 * b ^ 2) ≥ 0 := by
      nlinarith [sq_nonneg (b), sq_nonneg (sqrt 6 - sqrt 6), Real.sqrt_nonneg 6, h1, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    use (-4 * m * b + Real.sqrt (24 * m ^ 2 + 12 - 8 * b ^ 2)) / (2 * (1 + 2 * m ^ 2))
    use (m * ((-4 * m * b + Real.sqrt (24 * m ^ 2 + 12 - 8 * b ^ 2)) / (2 * (1 + 2 * m ^ 2))) + b)
    constructor
    · -- Show x^2 + 2 * y^2 = 3
      field_simp
      ring_nf
      rw [Real.sq_sqrt (by nlinarith)]
      <;> nlinarith
    · -- Show y = m * x + b
      ring_nf