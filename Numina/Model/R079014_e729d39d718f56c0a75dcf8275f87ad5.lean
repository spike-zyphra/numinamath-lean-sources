import Mathlib

open Real Set
open scoped Real

theorem algebra_183315 {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    arcsin (cos (arcsin x)) + arccos (sin (arccos x)) = π / 2 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : cos (arcsin x) = Real.sqrt (1 - x^2) := by 
    rw [Real.cos_arcsin]
    <;> ring_nf
    <;> nlinarith [Real.sqrt_nonneg (1 - x^2), sq_nonneg x]
  have h2 : sin (arccos x) = Real.sqrt (1 - x^2) := by 
    rw [Real.sin_arccos]
    <;> ring_nf
    <;> nlinarith [Real.sqrt_nonneg (1 - x^2), sq_nonneg x]
  rw [h1, h2]
  have h5 : arcsin (sqrt (1 - x^2)) + arccos (sqrt (1 - x^2)) = π / 2 := by
    have h6 : arcsin (sqrt (1 - x^2)) = π / 2 - arccos (sqrt (1 - x^2)) := by
      rw [show arcsin (sqrt (1 - x^2)) = π / 2 - arccos (sqrt (1 - x^2)) by 
          rw [Real.arcsin_eq_pi_div_two_sub_arccos]
      ]
    linarith [h6]
  linarith [h5]