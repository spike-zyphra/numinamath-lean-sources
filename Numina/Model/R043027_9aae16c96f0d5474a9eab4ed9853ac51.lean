import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_156151 (f : ℝ → ℝ) (hf : f = λ x => x^5 - 5*x^4 + 5*x^3 + 3)
  (a b : ℝ) (ha : a = -1) (hb : b = 2) :
  IsGreatest (image f (Icc a b)) 4 ∧ IsLeast (image f (Icc a b)) (-8) := by 
  rw [ha] at *
  rw [hb] at *
  constructor
  · -- Show 4 is greatest in the image
    constructor
    · -- Show 4 belongs to the image
      use 1
      constructor 
      · -- Show 1 ∈ [-1, 2]
        norm_num
      · -- Show f(1) = 4
        rw [hf]
        norm_num
    · -- Show it is greatest
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      have h1 : -1 ≤ x := by 
        have h1 : x ∈ Icc (-1 : ℝ) (2 : ℝ) := hx
        exact h1.1 
      have h2 : x ≤ 2 := by 
        have h1 : x ∈ Icc (-1 : ℝ) (2 : ℝ) := hx
        exact h1.2 
      rw [hf] at hfx 
      have hfx_eq : x^5 - 5*x^4 + 5*x^3 + 3 = y := by 
        simpa using hfx 
      have h3 : x^5 - 5*x^4 + 5*x^3 + 3 ≤ 4 := by
        nlinarith [sq_nonneg (x^2 - 2 * x + 1), sq_nonneg (x^2 - 2 * x + 2), sq_nonneg (x - 1),
                  sq_nonneg (x - 0), sq_nonneg (x - 2), sq_nonneg (x + 1),
                  sq_nonneg (x^2 - 1), sq_nonneg (x * (x - 1)), sq_nonneg ((x - 1) * (x - 2)),
                  sq_nonneg ((x) * (x - 2)), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg ((x - 1) * (x - 0)), 
                  mul_nonneg (show (0 : ℝ) ≤ (x + 1) by nlinarith) 
                                (show (0 : ℝ) ≤ (2 - x) by nlinarith)]
      linarith [hfx_eq, h3]
  · -- Show -8 is least in the image
    constructor 
    · -- Show -8 belongs to the image
      use -1
      constructor 
      · -- Show -1 ∈ [-1, 2]
        norm_num 
      · -- Show f(-1) = -8
        rw [hf]
        norm_num
    · -- Show it is least 
      intro y hy 
      rcases hy with ⟨x, hx, hfx⟩
      have h1 : -1 ≤ x := by 
        have h1 : x ∈ Icc (-1 : ℝ) (2 : ℝ) := hx 
        exact h1.1 
      have h2 : x ≤ 2 := by 
        have h1 : x ∈ Icc (-1 : ℝ) (2 : ℝ) := hx 
        exact h1.2 
      rw [hf] at hfx 
      have hfx_eq : x^5 - 5*x^4 + 5*x^3 + 3 = y := by 
        simpa using hfx 
      have h4 : x^5 - 5*x^4 + 5*x^3 + 3 ≥ -8 := by 
        nlinarith [sq_nonneg (x^2 - 2 * x + 1), sq_nonneg (x^2 - 2 * x + 2), sq_nonneg (x - 1),
                  sq_nonneg (x - 0), sq_nonneg (x - 2), sq_nonneg (x + 1),
                  sq_nonneg (x^2 - 1), sq_nonneg (x * (x - 1)), sq_nonneg ((x - 1) * (x - 2)),
                  sq_nonneg ((x) * (x - 2)), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg ((x - 1) * (x - 0)), 
                  mul_nonneg (show (0 : ℝ) ≤ (x + 1) by nlinarith) 
                                (show (0 : ℝ) ≤ (2 - x) by nlinarith)]
      linarith [hfx_eq, h4]