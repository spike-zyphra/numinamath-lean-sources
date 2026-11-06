import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_205381 (f : ℝ → ℝ) (hf : f = λ x => x + sqrt (1 - x^2)) :
    IsGreatest (image f (Icc (-1) 1)) (sqrt 2) := by
  constructor
  · -- Show that sqrt 2 is in the image
    use Real.sqrt 2 / 2
    constructor
    · -- Show that sqrt 2 / 2 ∈ [-1, 1]
      have h1 : Real.sqrt 2 / 2 ≥ -1 := by
        have h_pos : Real.sqrt 2 > 0 := by positivity
        linarith
      have h2 : Real.sqrt 2 / 2 ≤ 1 := by
        have h_val : Real.sqrt 2 < 2 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        linarith
      exact ⟨by linarith, by linarith⟩
    · -- Show that f (sqrt 2 / 2) = sqrt 2
      rw [hf]
      have h3 : (Real.sqrt 2 / 2 : ℝ) + Real.sqrt (1 - (Real.sqrt 2 / 2)^2) = Real.sqrt 2 := by
        have h4 : (1 - (Real.sqrt 2 / 2 : ℝ)^2) = (1 / 2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        rw [h4]
        have h5 : Real.sqrt ((1 / 2 : ℝ)) = (Real.sqrt 2 / 2 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        rw [h5]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      simpa using h3
  · -- Show that sqrt 2 is greatest
    intro y
    rintro ⟨x, hx, rfl⟩
    rw [hf]
    have h1 : -1 ≤ x := by
      linarith [hx.1, hx.2]
    have h2 : x ≤ 1 := by
      linarith [hx.1, hx.2]
    have h3 : 0 ≤ 1 - x^2 := by
      nlinarith
    have h4 : (x + Real.sqrt (1 - x^2) : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg (1 - x^2), Real.sqrt_nonneg 2, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (1 - x^2 : ℝ) by nlinarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
          Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
          sq_nonneg (x - Real.sqrt 2 / 2), sq_nonneg (Real.sqrt (1 - x^2) - Real.sqrt 2 / 2),
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)
          ]
    simpa using h4