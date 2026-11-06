import Mathlib

theorem algebra_94051 (x : ℝ) (hx : 1 / Real.cos x - Real.tan x = 2) :
    1 / Real.cos x + Real.tan x = 0.5 := by
  have htan : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan] at hx
  have h1 : Real.cos x ≠ 0 := by
    by_contra h
    have h2 : (1 / Real.cos x - Real.sin x / Real.cos x) = 0 := by
      rw [h]
      norm_num
    linarith [hx, h2]
  -- We can compute `1 - Real.sin x = 2 * Real.cos x` from `hx`.
  have eq1 : 1 - Real.sin x = 2 * Real.cos x := by
    have eq2 : (1 / Real.cos x - Real.sin x / Real.cos x) = (1 - Real.sin x) / Real.cos x := by
      field_simp [h1]
      <;> linarith
    rw [eq2] at hx
    have eq3 : (1 - Real.sin x) / Real.cos x = 2 := by
      linarith
    have eq4 : 1 - Real.sin x = 2 * Real.cos x := by
      field_simp [h1] at eq3 ⊢
      linarith [eq3]
    exact_mod_cast eq4
  have eq2 : Real.sin x = 1 - 2 * Real.cos x := by
    linarith [eq1]
  -- Use the Pythagorean identity `Real.sin x ^ 2 + Real.cos x ^ 2 = 1` to find `Real.cos x`.
  have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  rw [eq2] at h2
  have h3 : (1 - 2 * Real.cos x) ^ 2 + Real.cos x ^ 2 = 1 := by
    linarith [h2]
  have h4 : 5 * (Real.cos x) ^ 2 - 4 * (Real.cos x) = 0 := by
    nlinarith
  have h5 : Real.cos x * (5 * Real.cos x - 4) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Real.cos x = 0, which is a contradiction
    exfalso
    apply h1
    linarith
  · -- 5 * Real.cos x - 4 = 0, so Real.cos x = 4/5
    have cosx45 : Real.cos x = 4 / 5 := by
      linarith
    have sinx25 : Real.sin x = -3 / 5 := by
      rw [cosx45] at eq2
      linarith
    -- Now prove the final goal `1 / Real.cos x + Real.tan x = 0.5`.
    rw [htan]
    rw [cosx45, sinx25]
    norm_num