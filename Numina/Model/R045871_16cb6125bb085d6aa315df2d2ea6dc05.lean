import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12015 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (sqrt (1 + x) + sqrt (1 - x) + 2) * (sqrt (1 - x^2) + 1)) :
  IsLeast (image f (Icc 0 1)) (2 + sqrt 2) := by
  constructor
  · -- Show that 2 + sqrt 2 is in the image
    use 1
    constructor
    · norm_num
    · -- Compute f 1
      have h1 : f 1 = (sqrt (1 + (1 : ℝ)) + sqrt (1 - (1 : ℝ)) + 2) * (sqrt (1 - (1 : ℝ) ^ 2) + 1) := h₀ 1
      rw [h1]
      have h2 : sqrt (1 + (1 : ℝ)) = sqrt 2 := by norm_num
      have h3 : sqrt (1 - (1 : ℝ)) = 0 := by norm_num [sqrt_eq_zero]
      have h4 : sqrt (1 - (1 : ℝ) ^ 2) = 0 := by norm_num [sqrt_eq_zero]
      simp only [h2, h3, h4]
      ring_nf
      <;> norm_num

  · -- Show that 2 + sqrt 2 is a lower bound
    intro y
    rintro ⟨x, hx, hfx⟩

    rw [h₀ x] at hfx

    have h1 : 0 ≤ x := by
      have h1 : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
      have h2 : (0 : ℝ) ≤ x := h1.1
      linarith

    have h2 : x ≤ 1 := by
      have h1 : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
      have h2 : x ≤ (1 : ℝ) := h1.2
      linarith

    have h3 : 0 ≤ (1 + x : ℝ) := by linarith
    have h4 : 0 ≤ (1 - x : ℝ) := by linarith
    have h5 : 0 ≤ (1 - x^2 : ℝ) := by nlinarith
    have h6 : sqrt (1 + x) ≥ 0 := Real.sqrt_nonneg (1 + x)
    have h7 : sqrt (1 - x) ≥ 0 := Real.sqrt_nonneg (1 - x)
    have h8 : sqrt (1 - x^2) ≥ 0 := Real.sqrt_nonneg (1 - x^2)
    have h9 : sqrt (1 - x^2) + 1 ≥ 1 := by nlinarith [Real.sqrt_nonneg (1 - x^2)]

    have h10 : sqrt (1 + x) + sqrt (1 - x) ≥ Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg (1 + x), Real.sqrt_nonneg (1 - x), 
       Real.sq_sqrt (show (0 : ℝ) ≤ (1 + x) by linarith), 
       Real.sq_sqrt (show (0 : ℝ) ≤ (1 - x) by linarith), 
       Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
       sq_nonneg (sqrt (1 + x) - sqrt (1 - x)), 
       sq_nonneg (sqrt (1 + x) + sqrt (1 - x)), 
       mul_nonneg (Real.sqrt_nonneg (1 + x)) (Real.sqrt_nonneg (1 - x)), 
       sq_nonneg (sqrt (2 : ℝ)), 
       Real.sqrt_nonneg 2]
    
    have h11 : sqrt (1 + x) + sqrt (1 - x) + 2 ≥ Real.sqrt 2 + 2 := by linarith [Real.sqrt_nonneg 2]

    have h12 : (sqrt (1 + x) + sqrt (1 - x) + 2) * (sqrt (1 - x^2) + 1) ≥ (Real.sqrt 2 + 2) * 1 := by
      nlinarith [Real.sqrt_nonneg (1 - x^2), h9, h11, Real.sqrt_nonneg 2]

    have hfx_eq2 : (sqrt (1 + x) + sqrt (1 - x) + 2) * (sqrt (1 - x^2) + 1) = y := by linarith [hfx]
    linarith [hfx_eq2, h12]