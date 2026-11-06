import Mathlib

open Real Set
open scoped Real

theorem inequalities_249799 (x : Real) (hx : x ∈ Ioo 0 (π/2)) :
    1 + tan x < 1 / (1 - sin x) := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h2 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith
    linarith
  have h3 : sin x < 1 := by
    have h4 : sin x < sin (π / 2) := by
      apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals
        linarith [Real.pi_pos]
    have h5 : sin (π / 2) = 1 := by
      rw [sin_pi_div_two]
    linarith
  have h4 : 1 - sin x > 0 := by
    linarith
  have hx6 : tan x = sin x / cos x := by
    rw [tan_eq_sin_div_cos]
  rw [hx6]
  have h8 : sin x + cos x > 1 := by
    have h9 : sin x ^ 2 + cos x ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq x
    nlinarith [sq_pos_of_pos h1, sq_pos_of_pos h2, sq_nonneg (sin x - cos x), Real.sin_sq_add_cos_sq x, sq_pos_of_pos h1, sq_pos_of_pos h2]
  have hx7 : 1 + sin x / cos x < 1 / (1 - sin x) := by
    have h11 : (1 + sin x / cos x) * (1 - sin x) - 1 < 0 := by
      have h12 : (1 + sin x / cos x) * (1 - sin x) - 1 = (sin x / cos x) * (1 - sin x - cos x) := by
        field_simp
        <;> nlinarith [Real.sin_sq_add_cos_sq x, sq_pos_of_pos h1, sq_pos_of_pos h2]
      rw [h12]
      have h13 : sin x / cos x > 0 := by
        apply div_pos
        all_goals linarith
      have h14 : 1 - sin x - cos x < 0 := by
        nlinarith [h8]
      have h15 : (sin x / cos x) * (1 - sin x - cos x) < 0 := by
        apply mul_neg_of_pos_of_neg
        all_goals linarith [h13, h14]
      linarith
    have h13 : (1 + sin x / cos x) * (1 - sin x) < 1 := by
      nlinarith
    have h14 : 1 + sin x / cos x < 1 / (1 - sin x) := by
      apply (lt_div_iff₀ (by linarith)).mpr
      linarith
    exact h14
  exact_mod_cast hx7