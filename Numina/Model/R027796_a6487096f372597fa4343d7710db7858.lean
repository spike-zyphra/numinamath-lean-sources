import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_158839 (F : ℝ → ℝ → ℝ)
  (hF : F = λ x y => if x ∈ Icc 0 (π/2) ∧ y ∈ Icc 0 (π/2) then sin x * sin y else 0) :
  F (π/4) (π/3) - F (0) (π/3) - F (π/4) (π/6) + F (0) (π/6) =
  (sqrt 6 - sqrt 2)/4 := by
  have h1 : F (π/4) (π/3) = sin (π / 4) * sin (π / 3) := by
    rw [hF]
    have h1 : 0 ≤ π / 4 ∧ π / 4 ≤ π / 2 := by
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    have h2 : 0 ≤ π / 3 ∧ π / 3 ≤ π / 2 := by
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    simp [h1, h2]
  have h2 : F (0) (π / 3) = 0 := by
    rw [hF]
    have h1 : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ π / 2 := by
      constructor
      · linarith
      · linarith [Real.pi_pos]
    have h2 : 0 ≤ π / 3 ∧ π / 3 ≤ π / 2 := by
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    simp [h1, h2, sin_zero]
  have h3 : F (π / 4) (π / 6) = sin (π / 4) * sin (π / 6) := by
    rw [hF]
    have h1 : 0 ≤ π / 4 ∧ π / 4 ≤ π / 2 := by
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    have h2 : 0 ≤ π / 6 ∧ π / 6 ≤ π / 2 := by
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    simp [h1, h2]
  have h4 : F (0) (π / 6) = 0 := by 
    rw [hF]
    have h1 : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ π / 2 := by
      constructor
      · linarith 
      · linarith [Real.pi_pos]
    have h2 : 0 ≤ π / 6 ∧ π / 6 ≤ π / 2 := by
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    simp [h1, h2, sin_zero]
  have h8 : F (π/4) (π/3) = sin (π / 4) * sin (π / 3) := h1
  have h9 : F (0) (π/3) = 0 := h2
  have h10 : F (π/4) (π/6) = sin (π / 4) * sin (π / 6) := h3
  have h11 : F (0) (π/6) = 0 := h4
  simp only [h8, h9, h10, h11]
  rw [Real.sin_pi_div_four] at *
  rw [Real.sin_pi_div_three] at *
  rw [Real.sin_pi_div_six] at *
  have h12 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    calc
      Real.sqrt 2 * Real.sqrt 3 = Real.sqrt (2 * 3) := by
        rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt (6 : ℝ) := by
        norm_num
  have eq1 : Real.sqrt 2 / 2 * (Real.sqrt 3 / 2) - Real.sqrt 2 / 2 * (1 / 2) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
    have h14 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := h12
    field_simp [show Real.sqrt 2 ≠ 0 by positivity, show Real.sqrt 3 ≠ 0 by positivity] at *
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (2 : ℝ) > 0), 
      Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), 
      Real.sqrt_pos.mpr (show 0 < (6 : ℝ) by norm_num : (6 : ℝ) > 0), 
      sq_nonneg (Real.sqrt 6 - Real.sqrt 2), sq_nonneg (Real.sqrt 2), sq_nonneg (Real.sqrt 3), 
      h14, 
      Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num), 
      Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  linarith [eq1]