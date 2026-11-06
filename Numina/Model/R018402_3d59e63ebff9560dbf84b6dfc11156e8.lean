import Mathlib

theorem algebra_235619 (d c p : ℝ) (hc : c > 0) (hp : p > 0)
    (h1 : d / c = d / p + 2) (h2 : d / c = 30 / 60) :
    d / p = 10 := by

  have h3 : d / c = (30 : ℝ) / 60 := by linarith
  have h4 : d / c = 0.5 := by
    rw [h3]
    norm_num

  have h5 : d / p = -1.5 := by
    linarith [h1, h4]

  have h6 : d > 0 := by
    have h7 : d / c = 0.5 := h4
    have hc' : c > 0 := hc
    have h8 : d = 0.5 * c := by
      field_simp at h7 ⊢
      linarith
    nlinarith [hc']

  have h7 : d / p > 0 := by
    apply div_pos
    all_goals linarith

  linarith