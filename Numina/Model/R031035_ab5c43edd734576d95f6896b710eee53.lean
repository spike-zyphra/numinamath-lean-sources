import Mathlib


theorem algebra_137035 {a b c : ℝ} (h₀ : a ≠ -b) (h₁ : b ≠ -c) (h₂ : c ≠ -a)
    (h₃ : a * b / (a + b) = 2) (h₄ : b * c / (b + c) = 5) (h₅ : c * a / (c + a) = 9) :
    a * b * c / (a * b + b * c + c * a) = 180 / 73 := by

  have h6 : a + b ≠ 0 := by
    intro h
    apply h₀
    linarith

  have h7 : b + c ≠ 0 := by
    intro h
    apply h₁
    linarith

  have h8 : c + a ≠ 0 := by
    intro h
    apply h₂
    linarith

  have eq1 : (a + b) / (a * b) = 1 / 2 := by
    have h7' : a * b ≠ 0 := by
      by_contra h
      rw [h] at h₃
      norm_num at h₃
    have h9' : a + b ≠ 0 := h6
    field_simp [h7', h9'] at h₃ ⊢
    linarith

  have eq2 : (b + c) / (b * c) = 1 / 5 := by
    have h7' : b * c ≠ 0 := by
      by_contra h
      rw [h] at h₄
      norm_num at h₄
    have h9' : b + c ≠ 0 := h7
    field_simp [h7', h9'] at h₄ ⊢
    linarith

  have eq3 : (c + a) / (c * a) = 1 / 9 := by
    have h7' : c * a ≠ 0 := by
      by_contra h
      rw [h] at h₅
      norm_num at h₅
    have h9' : c + a ≠ 0 := h8
    field_simp [h7', h9'] at h₅ ⊢
    linarith

  have eq4 : 1 / a + 1 / b = 1 / 2 := by
    have h7' : a * b ≠ 0 := by
      by_contra h
      rw [h] at h₃
      norm_num at h₃
    have eq10 : (a + b) / (a * b) = 1 / 2 := eq1
    have ha0 : a ≠ 0 := by
      by_contra h
      rw [h] at h7'
      simp at h7'
    have hb0 : b ≠ 0 := by
      by_contra h
      rw [h] at h7'
      simp at h7'
    field_simp [ha0, hb0] at eq10 ⊢
    linarith

  have eq5 : 1 / b + 1 / c = 1 / 5 := by
    have h7' : b * c ≠ 0 := by
      by_contra h
      rw [h] at h₄
      norm_num at h₄
    have eq10 : (b + c) / (b * c) = 1 / 5 := eq2
    have hb0 : b ≠ 0 := by
      by_contra h
      rw [h] at h7'
      simp at h7'
    have hc0 : c ≠ 0 := by
      by_contra h
      rw [h] at h7'
      simp at h7'
    field_simp [hb0, hc0] at eq10 ⊢
    linarith

  have eq6 : 1 / c + 1 / a = 1 / 9 := by
    have h7' : c * a ≠ 0 := by
      by_contra h
      rw [h] at h₅
      norm_num at h₅
    have eq10 : (c + a) / (c * a) = 1 / 9 := eq3
    have hc0 : c ≠ 0 := by
      by_contra h
      rw [h] at h7'
      simp at h7'
    have ha0 : a ≠ 0 := by
      by_contra h
      rw [h] at h7'
      simp at h7'
    field_simp [hc0, ha0] at eq10 ⊢
    linarith

  have eq7 : 1 / a = 37 / 180 := by
    linarith [eq4, eq5, eq6]

  have eq8 : 1 / b = 53 / 180 := by
    linarith [eq4, eq5, eq6]

  have eq9 : 1 / c = -17 / 180 := by
    linarith [eq4, eq5, eq6]

  have ha1 : a ≠ 0 := by
    by_contra h
    rw [h] at eq7
    norm_num at eq7

  have hb1 : b ≠ 0 := by
    by_contra h
    rw [h] at eq8
    norm_num at eq8

  have hc1 : c ≠ 0 := by
    by_contra h
    rw [h] at eq9
    norm_num at eq9

  have ha2 : a = 180 / 37 := by
    field_simp [ha1] at eq7 ⊢
    linarith

  have hb2 : b = 180 / 53 := by
    field_simp [hb1] at eq8 ⊢
    linarith

  have hc2 : c = -180 / 17 := by
    field_simp [hc1] at eq9 ⊢
    linarith

  rw [ha2, hb2, hc2]
  field_simp
  norm_num