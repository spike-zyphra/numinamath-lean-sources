import Mathlib

open Real Set
open scoped Real

theorem algebra_186215 (α : ℝ) (h : sin (α/2) + cos (α/2) = 1.4) :
    sin α = 0.96 := by
  have h1 : sin (α / 2) + cos (α / 2) = (1.4 : ℝ) := by
    linarith
  have h2 : (sin (α / 2) + cos (α / 2)) ^ 2 = (1.4 : ℝ) ^ 2 := by
    rw [h1]
  have h3 : (sin (α / 2) + cos (α / 2)) ^ 2 = sin (α / 2) ^ 2 + cos (α / 2) ^ 2 + 2 * (sin (α / 2) * cos (α / 2)) := by 
    ring
  rw [h3] at h2 
  have h4 : sin (α / 2) ^ 2 + cos (α / 2) ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq (α / 2)
  rw [h4] at h2
  have h5 : sin α = 2 * sin (α / 2) * cos (α / 2) := by
    have h6 : sin α = sin (2 * (α / 2)) := by 
      ring_nf
    rw [h6]
    rw [Real.sin_two_mul (α / 2)]
    <;> ring_nf <;> simp [h]
  have h7 : (2 * sin (α / 2) * cos (α / 2) : ℝ) = (0.96 : ℝ) := by
    have h8 : (1.4 : ℝ) ^ 2 = (1.96 : ℝ) := by
      norm_num
    rw [h8] at h2 
    nlinarith 
  rw [h5]
  all_goals nlinarith [h7]