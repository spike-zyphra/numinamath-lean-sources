import Mathlib

open Real Set
open scoped Real

theorem algebra_12642 (α β : ℝ) (h₁ : sin α + sqrt 3 * sin β = 1) (h₂ : cos α + sqrt 3 * cos β = sqrt 3) :
    cos (α - β) = 0 := by
  have h3 : (sin α + Real.sqrt 3 * sin β) ^ 2 = 1 := by
    rw [h₁]
    norm_num
  have h4 : (cos α + Real.sqrt 3 * cos β) ^ 2 = 3 := by
    rw [h₂]
    norm_num
  have h5 : (sin α + Real.sqrt 3 * sin β) ^ 2 + (cos α + Real.sqrt 3 * cos β) ^ 2 = 4 := by
    nlinarith [h3, h4]
  have h6 : (sin α + Real.sqrt 3 * sin β) ^ 2 + (cos α + Real.sqrt 3 * cos β) ^ 2 =
      (sin α ^ 2 + cos α ^ 2) + 3 * (sin β ^ 2 + cos β ^ 2) + 2 * Real.sqrt 3 * (sin α * sin β + cos α * cos β) := by
    ring_nf
    <;> simp [Real.sqrt_sq, mul_add, add_mul, mul_comm, mul_assoc]
    <;> ring
  rw [h6] at h5
  have h7 : sin α ^ 2 + cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α
  have h8 : sin β ^ 2 + cos β ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq β
  rw [h7, h8] at h5
  have h9 : 2 * Real.sqrt 3 * (sin α * sin β + cos α * cos β) = 0 := by
    nlinarith
  have h10 : sin α * sin β + cos α * cos β = 0 := by
    have h11 : Real.sqrt 3 > 0 := by
      positivity
    nlinarith
  have h13 : cos (α - β) = cos α * cos β + sin α * sin β := by
    rw [cos_sub]
  rw [h13]
  linarith [h10]