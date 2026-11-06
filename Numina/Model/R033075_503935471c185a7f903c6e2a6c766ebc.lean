import Mathlib

theorem algebra_276210 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a ≠ b) (h' : a ≠ c) (h'' : b ≠ c) (h''' : a + b + c = 0) :
    ((a - b) / c + (b - c) / a + (c - a) / b) * (c / (a - b) + a / (b - c) + b / (c - a)) = 9 := by
  have hc2 : c = -a - b := by 
    linarith
  have h1 : a - b ≠ 0 := by
    intro h1
    apply h
    linarith
  have h2 : a - c ≠ 0 := by 
    intro h2
    apply h'
    linarith
  have h3 : b - c ≠ 0 := by 
    intro h3
    apply h''
    linarith
  have hcne : (-a - b) ≠ 0 := by
    intro h0
    apply hc
    linarith 
  have ha1 : a ≠ 0 := ha 
  have hb1 : b ≠ 0 := hb
  rw [hc2]
  have h4 : a - b ≠ 0 := h1
  have h5 : b - (-a - b) ≠ 0 := by 
    intro h3
    apply h''
    linarith
  have h6 : (-a - b) - a ≠ 0 := by 
    intro h3
    apply h'
    linarith
  field_simp [(show a ≠ 0 by exact ha), (show b ≠ 0 by exact hb), (show -a - b ≠ 0 by 
    intro h3
    apply hc
    linarith
  ), (show a - b ≠ 0 by 
    intro h1
    apply h
    linarith
  ), (show b - (-a - b) ≠ 0 by 
    intro h3
    apply h''
    linarith
  ), (show (-a - b) - a ≠ 0 by 
    intro h3
    apply h'
    linarith
  )
  ]
  <;> ring_nf
  <;> nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_nonneg (a * b), sq_nonneg (a + b), sq_nonneg (a * (a + b)), sq_nonneg (b * (a + b)), sq_pos_of_ne_zero (show a * b ≠ 0 by 
    apply mul_ne_zero 
    exact ha 
    exact hb
  ), sq_nonneg (a^2 - b^2)]