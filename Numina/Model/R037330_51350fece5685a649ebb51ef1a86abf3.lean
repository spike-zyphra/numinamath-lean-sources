import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_311914 :
  IsLeast {z : ℝ | ∃ x y, x > 0 ∧ y > 0 ∧ x^2 + y^2 = 1 ∧ z = (x^6 + y^6) / (x * y)} (1 / 2) := by
  constructor
  · -- Show that 1/2 is in the set.
    use Real.sqrt 2 / 2, Real.sqrt 2 / 2
    constructor
    · -- Show that sqrt(2)/2 > 0
      have h1 : Real.sqrt 2 / 2 > 0 := by
        have h2 : Real.sqrt 2 > 0 := by positivity
        linarith
      exact h1
    constructor
    · -- Show that sqrt(2)/2 > 0
      have h1 : Real.sqrt 2 / 2 > 0 := by
        have h2 : Real.sqrt 2 > 0 := by positivity
        linarith
      exact h1
    constructor
    · -- Show that (sqrt(2)/2)^2 + (sqrt(2)/2)^2 = 1
      have h1 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
        calc
          (Real.sqrt 2 / 2 : ℝ) ^ 2 = (Real.sqrt 2 ^ 2) / 4 := by ring_nf
          _ = 2 / 4 := by rw [Real.sq_sqrt]; linarith
          _ = 1 / 2 := by norm_num
      linarith [h1]
    · -- Show that (sqrt(2)/2)^6 + (sqrt(2)/2)^6 / (sqrt(2)/2 * sqrt(2)/2) = 1/2
      have h1 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
        calc
          (Real.sqrt 2 / 2 : ℝ) ^ 2 = (Real.sqrt 2 ^ 2) / 4 := by ring_nf
          _ = 2 / 4 := by rw [Real.sq_sqrt]; linarith
          _ = 1 / 2 := by norm_num
      have h2 : (Real.sqrt 2 / 2 : ℝ) ^ 6 = (1 / 8 : ℝ) := by
        calc
          (Real.sqrt 2 / 2 : ℝ) ^ 6 = ((Real.sqrt 2 / 2 : ℝ) ^ 2) ^ 3 := by ring
          _ = (1 / 2) ^ 3 := by rw [h1]
          _ = (1 / 8 : ℝ) := by norm_num
      have h3 : (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 2 / 2 : ℝ) = (1 / 2 : ℝ) := by
        calc
          (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 2 / 2 : ℝ) = (Real.sqrt 2 / 2 : ℝ) ^ 2 := by ring_nf
          _ = (1 / 2 : ℝ) := by rw [h1]
      rw [show (Real.sqrt 2 / 2 : ℝ) ^ 6 + (Real.sqrt 2 / 2 : ℝ) ^ 6 = (1 / 4 : ℝ) by
        rw [h2]
        linarith
      ]
      rw [h3]
      all_goals norm_num
  · -- Show that 1/2 is the minimum
    intro z hz
    rcases hz with ⟨x, y, hx, hy, h1, h2⟩
    have h3 : x * y > 0 := mul_pos hx hy
    have h4 : x^6 + y^6 = (1 - 3 * (x^2 * y^2)) := by
      have h5 : x^2 + y^2 = 1 := h1
      have h6 : x^6 + y^6 = (x^2 + y^2) ^ 3 - 3 * (x^2 * y^2) * (x^2 + y^2) := by
        ring
      rw [h5] at h6
      linarith [h6]
    have h7 : x * y ≤ (1 / 2 : ℝ) := by
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg (x^2 + y^2 - 1)]
    have h8 : (1 - 3 * (x^2 * y^2)) ≥ (1 / 2) * (x * y) := by
      nlinarith [sq_nonneg (x * y - 1 / 2), sq_nonneg (x^2 - y^2), sq_nonneg (x - y), h7, mul_pos hx hy]
    have h9 : (x^6 + y^6) / (x * y) ≥ (1 / 2 : ℝ) := by
      have h10 : (x^6 + y^6 : ℝ) = (1 - 3 * (x^2 * y^2)) := h4
      have h11 : (x^6 + y^6) = (1 - 3 * (x^2 * y^2)) := h4
      have h12 : (x * y) > 0 := h3
      apply (le_div_iff₀ h3).mpr
      nlinarith [h8]
    linarith [h2, h9]