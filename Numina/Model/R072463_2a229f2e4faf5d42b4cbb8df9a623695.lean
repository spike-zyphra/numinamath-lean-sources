import Mathlib

theorem algebra_280395 (a b c d : ℝ)
    (h₀ : a + b + c + d = 16.3)
    (h₁ : a = 1.5 * b)
    (h₂ : b / c = 3 / 4)
    (h₃ : c / d = 5 / 6) :
    d = 4.8 := by

  have hc : c ≠ 0 := by
    by_contra h
    rw [h] at h₂
    norm_num at h₂

  have hd : d ≠ 0 := by
    by_contra h
    rw [h] at h₃
    norm_num at h₃

  have h4 : 4 * b = 3 * c := by
    have hne : c ≠ 0 := hc
    field_simp at h₂
    linarith

  have h5 : 6 * c = 5 * d := by
    have hne : d ≠ 0 := hd
    field_simp at h₃
    linarith

  have ha : a = 1.5 * b := h₁
  have hc1 : c = (4 / 3) * b := by
    linarith

  have hd1 : d = (8 / 5) * b := by
    rw [hc1] at h5
    linarith

  rw [ha, hc1, hd1] at h₀
  ring_nf at h₀ ⊢

  linarith