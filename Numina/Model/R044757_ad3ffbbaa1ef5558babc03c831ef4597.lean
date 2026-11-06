import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_14013 {f : ℝ → ℝ}
  (h : ∀ x, x ≠ 0 → f x = f 1 * x + f 2 / x - 1) :
  IsLeast {y | ∃ x, x > 0 ∧ f x = y} (Real.sqrt 3 - 1) := by

  have h1 : f 2 = 1 := by
    have h2 := h 1 (by norm_num)
    norm_num at h2
    linarith

  have h2 : f 1 = 3 / 4 := by
    have h3 := h 2 (by norm_num)
    norm_num [h1] at h3
    linarith

  constructor
  · -- Show that √3 - 1 is achievable, by x = 2√3 / 3
    use 2 * Real.sqrt 3 / 3
    constructor
    · -- Show that 2 * √3 / 3 > 0
      have h3_pos : Real.sqrt 3 > 0 := by
        positivity
      positivity
    · -- Show that f(2 * √3 / 3) = √3 - 1
      have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      have h4 : Real.sqrt 3 > 0 := by positivity

      have eq1 := h (2 * Real.sqrt 3 / 3) (by
        have h5 : Real.sqrt 3 > 0 := by positivity
        positivity
      )
      rw [h2, h1] at eq1
      field_simp [h3, h4] at eq1 ⊢
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · -- Show that √3 - 1 is the least value in the image
    intro y hy
    rcases hy with ⟨x, hx, heq⟩
    have eq1 := h x (by linarith)
    rw [h2, h1] at eq1
    have eq2 : f x = 3 / 4 * x + 1 / x - 1 := by
      linarith [eq1]
    rw [eq2] at heq
    have h6 : 3 / 4 * x + 1 / x ≥ Real.sqrt 3 := by
      have h7 : (3 / 4 * x) ≥ 0 := by
        apply mul_nonneg
        norm_num
        linarith [hx]
      have h8 : (1 / x) ≥ 0 := by
        apply div_nonneg
        norm_num
        linarith [hx]
      have h7' : ((3 / 4 * x) + (1 / x)) ^ 2 ≥ 3 := by
        have h12 : ( (3 / 4 * x) * (1 / x) ) = 3 / 4 := by
          field_simp [hx]
          <;> nlinarith
        have h13 : ((3 / 4 * x) + (1 / x)) ^ 2 = ((3 / 4 * x) )^2 + ((1 / x) )^2 + 2 * ( (3 / 4 * x) * (1 / x) ) := by ring
        rw [h13, h12]
        have h14 : ((3 / 4 * x) )^2 + ((1 / x) )^2 ≥ 2 * (3 / 4) := by
          have h15 : ((3 / 4 * x) )^2 + ((1 / x) )^2 ≥ 2 * ( (3 / 4 * x) * (1 / x) ) := by
            nlinarith [ sq_nonneg ( (3 / 4 * x) - (1 / x) ) ]
          rw [h12] at h15
          linarith
        linarith
      have h8' : Real.sqrt ( ((3 / 4 * x) + (1 / x)) ^ 2 ) ≥ Real.sqrt (3) := by apply Real.sqrt_le_sqrt; linarith
      have h10 : Real.sqrt ( ((3 / 4 * x) + (1 / x)) ^ 2 ) = ( (3 / 4 * x) + (1 / x) ) := by
        rw [Real.sqrt_sq (show (0 : ℝ) ≤ ( (3 / 4 * x) + (1 / x) ) by 
          linarith [h7, h8] 
        )]
      have h9 : ( (3 / 4 * x) + (1 / x) ) ≥ 0 := by
        linarith [h7, h8]
      linarith [h8', h10, Real.sqrt_nonneg 3]
    linarith [Real.sqrt_nonneg 3, heq, h6]