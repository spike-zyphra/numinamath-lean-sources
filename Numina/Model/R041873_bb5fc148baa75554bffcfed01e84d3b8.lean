import Mathlib

open BigOperators Real Set

lemma lemma_1 (x : ℝ) :
    x^2 + 8 * x - 1 > 0 ↔ x > sqrt 17 - 4 ∨ x < -sqrt 17 - 4 := by
  constructor
  ·
    intro h
    have h2 : x ^ 2 + 8 * x - 1 = (x + 4) ^ 2 - 17 := by
      ring
    rw [h2] at h
    have h3 : (x + 4) ^ 2 > 17 := by linarith
    by_contra h4
    push_neg at h4
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 17), Real.sqrt_nonneg 17, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17), sq_nonneg (x + 4 - sqrt 17), sq_nonneg (x + 4 + sqrt 17), sq_nonneg (x + 4)]
  ·
    rintro (h | h)
    ·
      have h2 : x ^ 2 + 8 * x - 1 = (x + 4) ^ 2 - 17 := by
        ring
      have h3 : (x + 4) ^ 2 > 17 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (17 : ℝ) by norm_num), Real.sqrt_nonneg 17, Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num), sq_nonneg (x + 4 - sqrt 17), sq_nonneg (x + 4 + sqrt 17)]
      linarith [h3, (show x ^ 2 + 8 * x - 1 = (x + 4) ^ 2 - 17 by ring)]
    ·
      have h2 : x ^ 2 + 8 * x - 1 = (x + 4) ^ 2 - 17 := by
        ring
      have h3 : (x + 4) ^ 2 > 17 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (17 : ℝ) by norm_num), Real.sqrt_nonneg 17, Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num), sq_nonneg (x + 4 - sqrt 17), sq_nonneg (x + 4 + sqrt 17)]
      linarith [h3, (show x ^ 2 + 8 * x - 1 = (x + 4) ^ 2 - 17 by ring)]


theorem inequalities_309728 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, (x ≠ 0 ∨ y ≠ 0) → f x y = 5 * x ^ 2 + 8 * x * y + 3 * y ^ 2 + lambda * (x ^ 2 + y ^ 2))
  (h₁ : ∀ x y, (x ≠ 0 ∨ y ≠ 0) → f x y > 0) :
  lambda > sqrt 17 - 4 := by
  by_contra h
  push_neg at h
  have h2 := h₁ ((1 - Real.sqrt 17) / 4) (1 : ℝ) (by
    right
    norm_num
  )
  have h5 := h₀ ((1 - Real.sqrt 17) / 4) (1 : ℝ) (by
    right
    norm_num
  )
  have h_eq : 5 * ((1 - Real.sqrt 17) / 4) ^ 2 + 8 * ((1 - Real.sqrt 17) / 4) * (1 : ℝ) + 3 * (1 : ℝ) ^ 2 + lambda * (((1 - Real.sqrt 17) / 4) ^ 2 + (1 : ℝ) ^ 2) = 
          f ((1 - Real.sqrt 17) / 4) (1 : ℝ) := by 
    linarith [h5]
  have h6 : 5 * ((1 - Real.sqrt 17) / 4) ^ 2 + 8 * ((1 - Real.sqrt 17) / 4) * (1 : ℝ) + 3 * (1 : ℝ) ^ 2 + lambda * (((1 - Real.sqrt 17) / 4) ^ 2 + (1 : ℝ) ^ 2) ≤ (0 : ℝ) := by 
    nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num),
      sq_nonneg (lambda - (Real.sqrt 17 - 4)), 
      sq_nonneg ((1 - Real.sqrt 17) / 4 + 4), Real.sqrt_pos.mpr (show 0 < (17: ℝ) by norm_num),
      h, Real.sq_sqrt (show (0 : ℝ) ≤ (17: ℝ) by norm_num)
    ]
  nlinarith [h_eq, h2, h6, Real.sqrt_pos.mpr (show 0 < (17: ℝ) by norm_num), Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17: ℝ) by norm_num)]