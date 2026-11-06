import Mathlib

theorem algebra_224642 {a b c : ℝ} (habc : a ≠ b ∧ b ≠ c ∧ c ≠ a)
    (h : a + b + c = 0) :
    a^3 * (a + c) * (a + b) / ((a - c) * (a - b)) +
    b^3 * (b + a) * (b + c) / ((b - a) * (b - c)) +
    c^3 * (c + a) * (c + b) / ((c - a) * (c - b)) = a * b * c := by
  have ha1 : a - b ≠ 0 := by
    intro h1
    apply habc.1
    linarith
  have ha2 : a - c ≠ 0 := by
    intro h1
    apply habc.2.2
    linarith
  have hb1 : b - a ≠ 0 := by
    intro h1
    apply habc.1
    linarith
  have hb2 : b - c ≠ 0 := by
    intro h1
    apply habc.2.1
    linarith
  have hc1 : c - a ≠ 0 := by
    intro h1
    apply habc.2.2
    linarith
  have hc2 : c - b ≠ 0 := by
    intro h1
    apply habc.2.1
    linarith
  have hc : c = -a - b := by 
    linarith
  have ha2' : a - (-a - b) ≠ 0 := by
    intro h1
    have h1' : c = a := by 
      linarith [h1, hc]
    have h2' : c ≠ a := habc.2.2
    contradiction
  have hb2' : b - (-a - b) ≠ 0 := by 
    intro h1
    have h1' : c = b := by 
      linarith [h1, hc]
    have h2' : b ≠ c := habc.2.1
    tauto
  have hc1' : (-a - b) - a ≠ 0 := by 
    intro h1
    have h1' : c = a := by 
      linarith [h1, hc]
    have h2' : c ≠ a := habc.2.2
    contradiction
  have hc2' : (-a - b) - b ≠ 0 := by 
    intro h1
    have h1' : c = b := by 
      linarith [h1, hc]
    have h2' : b ≠ c := habc.2.1
    tauto
  rw [hc]
  field_simp [(show a - (-a - b) ≠ 0 by
    intro h1
    have h1' : c = a := by 
      linarith [h1, (show c = -a - b by linarith)]
    have h2' : c ≠ a := habc.2.2
    contradiction
  ), (show a - b ≠ 0 by
    intro h1
    apply habc.1
    linarith
  ), (show b - a ≠ 0 by
    intro h1
    apply habc.1
    linarith
  ), (show b - (-a - b) ≠ 0 by
    intro h1
    have h1' : c = b := by 
      linarith [h1, (show c = -a - b by linarith)]
    have h2' : b ≠ c := habc.2.1
    tauto
  ), (show (-a - b) - a ≠ 0 by
    intro h1
    have h1' : c = a := by 
      linarith [h1, (show c = -a - b by linarith)]
    have h2' : c ≠ a := habc.2.2
    contradiction
  ), (show (-a - b) - b ≠ 0 by
    intro h1
    have h1' : c = b := by 
      linarith [h1, (show c = -a - b by linarith)]
    have h2' : b ≠ c := habc.2.1
    tauto
  )
  ]
  <;> nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h1
      apply habc.1
      linarith
    ), sq_pos_of_ne_zero (show (a - (-a - b)) ≠ 0 by
      intro h1
      have h1' : c = a := by 
        linarith [h1, (show c = -a - b by linarith)]
      have h2' : c ≠ a := habc.2.2
      contradiction
    ), sq_pos_of_ne_zero (show b - a ≠ 0 by
      intro h1
      apply habc.1
      linarith
    ), sq_pos_of_ne_zero (show b - (-a - b) ≠ 0 by
      intro h1
      have h1' : c = b := by 
        linarith [h1, (show c = -a - b by linarith)]
      have h2' : b ≠ c := habc.2.1
      tauto
    )
  ]