import Mathlib

theorem other_286948 (a b c d e : ℝ)
    (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (he : e > 0)
    (h1 : a / b = 5 / 9) (h2 : b / c = 5 / 12) (h3 : c / d = 5 / 15)
    (h4 : d / e = 5 / 18) :
    e > a ∧ e > b ∧ e > c ∧ e > d := by

  have h10 : e > d := by
    have h4' : d / e = 5 / 18 := h4
    have pos1 : e > 0 := he
    have pos2 : d > 0 := hd
    have h11 : d = (5 / 18) * e := by
      field_simp at h4'
      linarith
    nlinarith

  have h12 : e > c := by
    have h3' : c / d = 5 / 15 := h3
    have pos1 : d > 0 := hd
    have pos2 : c > 0 := hc
    have h13 : c = (5 / 15) * d := by 
      field_simp at h3'
      linarith
    have h14 : c < d := by 
      nlinarith [h13, pos1]
    linarith [h10, h14]

  have h15 : e > b := by
    have h2' : b / c = 5 / 12 := h2
    have pos1 : c > 0 := hc
    have pos2 : b > 0 := hb
    have h16 : b = (5 / 12) * c := by 
      field_simp at h2'
      linarith
    have h17 : b < e := by 
      nlinarith [h12, h16]
    linarith [h17]

  have h18 : e > a := by
    have h1' : a / b = 5 / 9 := h1
    have pos1 : b > 0 := hb
    have pos2 : a > 0 := ha
    have h19 : a = (5 / 9) * b := by 
      field_simp at h1'
      linarith
    nlinarith [h19, h15]

  exact ⟨h18, h15, h12, h10⟩