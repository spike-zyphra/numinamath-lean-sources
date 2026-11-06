import Mathlib

theorem calculus_12347 {x : ℝ} (h : Real.cos x ≠ 0) (h' : 1 / Real.cos x + Real.tan x = 5 / 2) :
    1 / Real.cos x - Real.tan x = 2 / 5 := by
  have htan : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan] at h'
  have eq1 : 1 / Real.cos x + Real.sin x / Real.cos x = (1 + Real.sin x) / Real.cos x := by
    have h1 : Real.cos x ≠ 0 := h
    field_simp [h1]
    <;> ring
  rw [eq1] at h'
  have eq2 : Real.cos x ≠ 0 := h
  have eq3 : 2 * (1 + Real.sin x) = 5 * Real.cos x := by
    have h1 : Real.cos x ≠ 0 := h
    have eq4 : (1 + Real.sin x) / Real.cos x = 5 / 2 := by
      linarith [h']
    field_simp [h1] at eq4 ⊢
    linarith
  have eq4 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have eq5 : Real.sin x = (5 * Real.cos x - 2) / 2 := by
    linarith [eq3]
  rw [eq5] at eq4
  have eq6 : (Real.cos x) * (29 * Real.cos x - 20) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq6) with eq7 eq8
  · -- Case cos x = 0, which contradicts h
    exfalso
    apply h
    linarith
  · -- Case 29 * cos x - 20 = 0
    have eq9 : Real.cos x = 20 / 29 := by
      linarith
    have eq10 : Real.sin x = 21 / 29 := by
      rw [eq9] at eq5
      linarith
    rw [htan]
    have eq11 : 1 / Real.cos x - (Real.sin x / Real.cos x) = (1 - Real.sin x) / Real.cos x := by
      have h1 : Real.cos x ≠ 0 := h
      field_simp [h1]
      <;> ring
    rw [eq11]
    rw [eq9, eq10]
    norm_num