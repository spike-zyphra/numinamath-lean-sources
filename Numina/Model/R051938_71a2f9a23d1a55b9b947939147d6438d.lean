import Mathlib

theorem algebra_310086 (α β : ℝ) (h₁ : Real.sin α + Real.sqrt 3 * Real.sin β = 1) (h₂ : Real.cos α + Real.sqrt 3 * Real.cos β = Real.sqrt 3) :
    Real.cos (α - β) = 0 := by
  have h3 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h4 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β

  have eq1 : (Real.sin α + Real.sqrt 3 * Real.sin β) ^ 2 = 1 := by
    rw [h₁]
    all_goals norm_num

  have eq2 : (Real.cos α + Real.sqrt 3 * Real.cos β) ^ 2 = 3 := by
    rw [h₂]
    all_goals norm_num

  have eq3 : (Real.sin α + Real.sqrt 3 * Real.sin β) ^ 2 + (Real.cos α + Real.sqrt 3 * Real.cos β) ^ 2 = 4 := by
    linarith [eq1, eq2]

  have eq4 : (Real.sin α + Real.sqrt 3 * Real.sin β) ^ 2 + (Real.cos α + Real.sqrt 3 * Real.cos β) ^ 2 =
      (Real.sin α ^ 2 + Real.cos α ^ 2) + 3 * (Real.sin β ^ 2 + Real.cos β ^ 2) + 2 * Real.sqrt 3 * (Real.sin α * Real.sin β + Real.cos α * Real.cos β) := by
    ring_nf
    <;> simp [mul_pow, Real.sqrt_sq]
    <;> ring

  rw [eq4] at eq3
  rw [h3, h4] at eq3

  have eq5 : 2 * Real.sqrt 3 * (Real.sin α * Real.sin β + Real.cos α * Real.cos β) = 0 := by
    nlinarith

  have eq6 : Real.sin α * Real.sin β + Real.cos α * Real.cos β = 0 := by
    have h7 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
    nlinarith

  have h : Real.cos (α - β) = Real.cos α * Real.cos β + Real.sin α * Real.sin β := Real.cos_sub α β
  rw [h]
  linarith [eq6]