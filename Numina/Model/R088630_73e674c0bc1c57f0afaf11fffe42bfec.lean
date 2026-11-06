import Mathlib

theorem algebra_5050 (x : ℝ) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (h : Real.tan x = 5 / 12) :
    3 * Real.cos x - 4 * Real.sin x = 16 / 13 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : Real.cos x > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [hx1]
    · linarith [hx2]
  have h2 : Real.sin x = 5 / 12 * Real.cos x := by
    have htan : Real.tan x = Real.sin x / Real.cos x := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan] at h
    have hne : Real.cos x ≠ 0 := by linarith
    field_simp [hne] at h ⊢
    nlinarith
  have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  rw [h2] at h3
  have h4 : Real.cos x ^ 2 = 144 / 169 := by
    nlinarith
  have h5 : Real.cos x = 12 / 13 := by
    nlinarith [h1, h4]
  have h6 : Real.sin x = 5 / 13 := by
    rw [h5] at h2
    nlinarith
  rw [h5, h6]
  norm_num