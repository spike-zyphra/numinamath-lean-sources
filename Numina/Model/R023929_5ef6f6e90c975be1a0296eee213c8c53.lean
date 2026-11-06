import Mathlib

theorem algebra_99796 {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) (h4 : c = a + b) :
    ((a - b) / c + (b - c) / a + (c - a) / b) * (c / (a - b) + a / (b - c) + b / (c - a)) = 1 := by 
  have ha1 : c = a + b := h4
  have h5 : a - b ≠ 0 := by
    intro h
    apply h1
    nlinarith
  have h6 : a + b ≠ 0 := by
    by_contra h
    have h8 : c = 0 := by 
      linarith [ha1, h]
    contradiction
  have h7 : b - c ≠ 0 := by
    by_contra h
    have h8 : b = c := by
      nlinarith
    tauto
  have h8 : c - a ≠ 0 := by
    by_contra h
    have h9 : c = a := by
      nlinarith
    have h10 : a = c := by 
      nlinarith
    tauto
  have eq1 : ((a - b) / c + (b - c) / a + (c - a) / b) * (c / (a - b) + a / (b - c) + b / (c - a)) = 1 := by 
    rw [show c = a + b by linarith [h4]] 
    have h18 : (a + b : ℚ) ≠ 0 := h6
    have h19 : a ≠ 0 := ha 
    have h20 : b ≠ 0 := hb 
    field_simp [(show a ≠ 0 by assumption), (show b ≠ 0 by assumption), 
      (show a + b ≠ 0 by assumption), 
      (show a - b ≠ 0 by 
        intro h
        apply h1 
        linarith 
      ), (show b - (a + b) ≠ 0 by 
        intro h 
        apply h3 
        linarith 
      ), (show (a + b) - a ≠ 0 by 
        intro h 
        have h11 : b = 0 := by 
          linarith 
        contradiction 
      )
    ]
    <;> ring_nf 
    <;> nlinarith 
  linarith [eq1]