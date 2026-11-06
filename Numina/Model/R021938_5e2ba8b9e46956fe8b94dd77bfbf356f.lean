import Mathlib

theorem algebra_276875 (x : ℝ) (hx : Real.sin x + Real.cos x = 1 / 5) (hxp : 0 ≤ x ∧ x < Real.pi) :
    Real.tan x = -4 / 3 := by
  have h1 : 0 ≤ x := hxp.1
  have h2 : x < Real.pi := hxp.2
  have h3 : Real.sin x ≥ 0 := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    linarith
    linarith
  have h4 : Real.sin x = 4 / 5 := by
    have eq1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have eq2 : Real.cos x = 1 / 5 - Real.sin x := by
      linarith [hx]
    rw [eq2] at eq1
    have hquadratic : 50 * (Real.sin x) ^ 2 - 10 * (Real.sin x) - 24 = 0 := by
      nlinarith
    have h6 : (Real.sin x - 4 / 5) * (Real.sin x + 3 / 5) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- Case where sin x = 4/5.
      linarith
    · -- Case where sin x = -3/5, which contradicts with 0 ≤ x < Real.pi
      nlinarith [Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ x) (by linarith : x ≤ Real.pi), h2]
  have h8 : Real.cos x = -3 / 5 := by
    have h9 : Real.sin x = 4 / 5 := h4
    linarith [hx, h9]
  have h9 : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
  rw [h9]
  rw [h4, h8]
  all_goals norm_num