import Mathlib

open Real Set
open scoped Real

theorem inequalities_241935 (x : ℝ) (hx : x ∈ Ioo 0 (π/2)) :
    cos x ^ 2 / tan x + sin x ^ 2 * tan x ≥ 1 := by
  rcases hx with ⟨hx1, hx2⟩ -- `hx1` : 0 < x, `hx2` : x < π/2 
  have h1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h2 : cos x > 0 := by 
    apply cos_pos_of_mem_Ioo
    constructor
    linarith
    linarith
  have htan_pos : tan x > 0 := by
    rw [tan_eq_sin_div_cos]
    apply div_pos
    all_goals linarith
  -- Express $\tan x$ in terms of $\sin x$ and $\cos x$
  have htan_def : tan x = sin x / cos x := by 
    rw [tan_eq_sin_div_cos]
  have eq1 : cos x ^ 2 / tan x = cos x ^ 3 / sin x := by 
    have h_eq : cos x ^ 2 / tan x = cos x ^ 3 / sin x := by
      rw [htan_def]
      have h3 : cos x ≠ 0 := by linarith [h2]
      have h4 : sin x ≠ 0 := by linarith [h1]
      field_simp [h3, h4]
      <;> ring
    linarith [h_eq]
  have eq2 : sin x ^ 2 * tan x = sin x ^ 3 / cos x := by 
    have h_eq : sin x ^ 2 * tan x = sin x ^ 3 / cos x := by
      rw [htan_def]
      have h3 : cos x ≠ 0 := by linarith [h2]
      have h4 : sin x ≠ 0 := by linarith [h1]
      field_simp [h3, h4]
      <;> ring
    linarith [h_eq]
  have eq3 : cos x ^ 2 / tan x + sin x ^ 2 * tan x = (cos x ^ 3 / sin x) + (sin x ^ 3 / cos x) := by 
    rw [eq1, eq2]
  have eq4 : (cos x ^ 3 / sin x) + (sin x ^ 3 / cos x) = (cos x ^ 4 + sin x ^ 4) / (sin x * cos x) := by 
    have h3 : cos x ≠ 0 := by linarith [h2]
    have h4 : sin x ≠ 0 := by linarith [h1]
    field_simp [h3, h4]
    <;> ring 
  have h3 : cos x ^ 4 + sin x ^ 4 ≥ sin x * cos x := by 
    nlinarith [sq_nonneg (cos x ^ 2 - sin x ^ 2), sq_nonneg (cos x - sin x), sq_nonneg (cos x * sin x - 1/2), sq_nonneg (cos x * sin x - 1/4), sq_nonneg (cos x - sin x), sq_nonneg (cos x + sin x), sq_nonneg (cos x - sin x), sq_nonneg (cos x * sin x), sq_nonneg (cos x * sin x - 1/4), sq_nonneg (cos x * sin x - 1/2), Real.sin_sq_add_cos_sq x, mul_pos h1 h2, sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1)]
  have h4 : (cos x ^ 4 + sin x ^ 4) / (sin x * cos x) ≥ 1 := by 
    have htan_pos2 : sin x * cos x > 0 := by
      nlinarith [h1, h2]
    apply (le_div_iff₀ htan_pos2).mpr
    nlinarith [h3, Real.sin_sq_add_cos_sq x]
  rw [eq3]
  rw [eq4]
  exact h4