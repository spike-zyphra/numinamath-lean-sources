import Mathlib

theorem algebra_297941 (y : ℝ → ℝ) (hy : y = fun x => 3 * Real.sin x - 4 * Real.cos x)
    (x0 : ℝ) (hx0 : DifferentiableAt ℝ y x0) (hmax : ∀ x, y x ≤ y x0) :
    Real.tan x0 = -3 / 4 := by
  have h1 : ∀ x, y x = 3 * Real.sin x - 4 * Real.cos x := by 
    intro x
    rw [hy]
  have eq1 := hmax (Real.arcsin (3 / 5))
  have eq1' : y (Real.arcsin (3 / 5)) ≤ y x0 := by simpa using eq1
  have eq1'' : y (Real.arcsin (3 / 5)) = 3 * Real.sin (Real.arcsin (3 / 5)) - 4 * Real.cos (Real.arcsin (3 / 5)) := by 
    rw [hy]
  rw [eq1''] at eq1'
  have h3 : Real.sin (Real.arcsin (3 / 5)) = 3 / 5 := by
    apply Real.sin_arcsin
    norm_num
    norm_num
  have h4 : Real.cos (Real.arcsin (3 / 5)) = 4 / 5 := by
    have h5 : Real.cos (Real.arcsin (3 / 5)) = Real.sqrt (1 - (3 / 5) ^ 2) := by 
      rw [Real.cos_arcsin]
      <;> ring_nf
      <;> norm_num
      <;> ring
    rw [h5]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  rw [h3, h4] at eq1'
  have eq2 := hmax (Real.arccos (-4 / 5))
  have eq2' : y (Real.arccos (-4 / 5)) ≤ y x0 := by simpa using eq2
  have eq2'' : y (Real.arccos (-4 / 5)) = 3 * Real.sin (Real.arccos (-4 / 5)) - 4 * Real.cos (Real.arccos (-4 / 5)) := by 
    rw [hy]
  rw [eq2''] at eq2'
  have h5 : Real.cos (Real.arccos (-4 / 5)) = -4 / 5 := by
    apply Real.cos_arccos
    linarith
    linarith
  have h6 : Real.sin (Real.arccos (-4 / 5)) = 3 / 5 := by 
    have h7 : Real.sin (Real.arccos (-4 / 5)) = Real.sqrt (1 - (-4 / 5) ^ 2) := by
      rw [Real.sin_arccos]
      <;> ring_nf <;> norm_num <;> ring
    rw [h7]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h5, h6] at eq2'
  have eq3' : y x0 = 3 * Real.sin x0 - 4 * Real.cos x0 := by 
    rw [hy]
  have h7 : (Real.sin x0) ^ 2 + (Real.cos x0) ^ 2 = 1 := Real.sin_sq_add_cos_sq x0
  -- Now combining all these.
  rw [eq3'] at eq2' -- This gives 3*(3/5) -4*(-4/5) <= 3*sinx0 -4*cosx0
  rw [eq3'] at eq1' -- Similarly
  have eq8 : Real.sin x0 = 3 / 5 := by
    nlinarith [sq_nonneg (Real.sin x0 - 3 / 5), sq_nonneg (Real.cos x0 + 4 / 5), Real.sin_sq_add_cos_sq x0]
  -- Now we can get cosx0 using fundamental relation
  have eq9 : Real.cos x0 = -4 / 5 := by 
    nlinarith [Real.sin_sq_add_cos_sq x0, eq8]
  rw [Real.tan_eq_sin_div_cos]
  rw [eq8, eq9]
  all_goals norm_num
  all_goals norm_num