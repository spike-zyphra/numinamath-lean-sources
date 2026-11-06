import Mathlib

theorem algebra_13377 (x : Real) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (h : Real.tan x = 7 / 24) :
    (Real.sin x + 3) / (5 - Real.cos x) = 82 / 101 := by 
  rcases hx with ⟨hx1, hx2⟩
  have htan : Real.cos x ≠ 0 := by
    by_contra h1
    have htan0 : Real.tan x = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h1]
    rw [htan0] at h
    norm_num at h
  have htan2 : Real.sin x / Real.cos x = 7 / 24 := by 
    rw [Real.tan_eq_sin_div_cos] at h 
    linarith
  have h1 : Real.sin x = 7 / 24 * Real.cos x := by
    have htan2' : Real.sin x / Real.cos x = 7 / 24 := htan2
    have : Real.sin x = (7 / 24) * Real.cos x := by
      field_simp [htan] at htan2' ⊢
      linarith
    linarith
  have h2 : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
  have h3 : Real.cos x > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · -- Show that -π/2 < x
      linarith [Real.pi_pos, hx1]
    · -- Show that x < π/2
      linarith [Real.pi_pos, hx2]
  rw [h1] at h2
  have h4 : Real.cos x ^ 2 = 576 / 625 := by
    nlinarith
  have h5 : Real.cos x = 24 / 25 := by 
    nlinarith [h4, h3]
  have h6 : Real.sin x = 7 / 25 := by 
    rw [h5] at h1
    linarith
  rw [h6, h5]
  norm_num
  all_goals field_simp
  all_goals norm_num