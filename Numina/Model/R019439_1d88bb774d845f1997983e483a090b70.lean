import Mathlib

theorem algebra_940 {a b c : ℝ} (ha : a ≠ -b) (hb : b ≠ -c) (hc : c ≠ -a)
    (h1 : a * b / (a + b) = 3) (h2 : b * c / (b + c) = 4) (h3 : c * a / (c + a) = 5) :
    a * b * c / (a * b + b * c + c * a) = 120 / 47 := by

  have h1' : a + b ≠ 0 := by
    intro h
    apply ha
    linarith
  have h2' : b + c ≠ 0 := by
    intro h
    apply hb
    linarith
  have h3' : c + a ≠ 0 := by
    intro h
    apply hc
    linarith

  -- From $\frac{ab}{a+b} = 3$ to $ab = 3(a+b)$
  have h11 : a * b = 3 * (a + b) := by
    have h1' : a + b ≠ 0 := by
      intro h
      apply ha
      linarith
    field_simp [h1'] at h1
    linarith

  -- From $\frac{bc}{b+c} = 4$ to $bc = 4(b+c)$
  have h22 : b * c = 4 * (b + c) := by
    have h2' : b + c ≠ 0 := by
      intro h
      apply hb
      linarith
    field_simp [h2'] at h2
    linarith
  
  -- From $\frac{ca}{c+a} = 5$ to $ca = 5(c+a)$
  have h33 : c * a = 5 * (c + a) := by
    have h3' : c + a ≠ 0 := by
      intro h
      apply hc
      linarith
    field_simp [h3'] at h3
    linarith
  
  -- Show that a, b, c are non-zero
  have ha1 : a ≠ 0 := by
    by_contra h
    have h4 : a = (0 : ℝ) := by linarith
    rw [h4] at h11
    have hb1 : b = 0 := by
      nlinarith
    -- Show that a = 0 and b = 0 contradicts a + b ≠ 0
    have hb1' : b = 0 := hb1
    have ha1' : a = 0 := by linarith [h4]
    have h44 : a + b = 0 := by
      linarith [hb1', ha1']
    have h55 : a + b ≠ 0 := h1'
    contradiction
  
  have hb1 : b ≠ 0 := by
    by_contra h
    have h5 : b = (0 : ℝ) := by linarith
    rw [h5] at h11
    -- Show that b = 0 leads to a = 0, contradiction with a + b ≠ 0
    have h6 : a = 0 := by
      nlinarith
    -- Show that a = 0 and b = 0 contradicts a + b ≠ 0
    have hb1' : b = 0 := by linarith [h5]
    have ha1' : a = 0 := by linarith [h6]
    have h44 : a + b = 0 := by
      linarith [hb1', ha1']
    have h55 : a + b ≠ 0 := h1'
    contradiction
  
  have hc1 : c ≠ 0 := by 
    by_contra h
    have h6 : c = (0 : ℝ) := by linarith
    rw [h6] at h33
    have h7 : a = 0 := by 
      nlinarith 
    -- Show that a = 0 and c = 0 contradicts c + a ≠ 0 
    have ha1' : a = 0 := by linarith [h7]
    have hc1' : c = 0 := by linarith [h6]
    have h44 : c + a = 0 := by
      linarith [hc1', ha1']
    have h55 : c + a ≠ 0 := h3'
    contradiction
  
  -- Transform equations to linear equations in reciprocals
  have eq1' : 1 / a + 1 / b = 1 / 3 := by
    field_simp [ha1, hb1] at h11 ⊢
    nlinarith

  have eq2' : 1 / b + 1 / c = 1 / 4 := by
    have hb1' : b ≠ 0 := hb1
    have hc1' : c ≠ 0 := hc1
    field_simp [hb1', hc1'] at h22 ⊢
    nlinarith

  have eq3' : 1 / c + 1 / a = 1 / 5 := by
    have ha1' : a ≠ 0 := ha1
    have hc1' : c ≠ 0 := hc1
    field_simp [ha1', hc1'] at h33 ⊢
    nlinarith
  
  -- Sum the reciprocal equations to find $\frac{1}{a} + \frac{1}{b} + \frac{1}{c}$
  have h4 : 1 / a + 1 / b + 1 / c = 47 / 120 := by 
    linarith [eq1', eq2', eq3']

  have h5 : a * b + b * c + c * a = a * b * c * (1 / a + 1 / b + 1 / c) := by 
    field_simp [ha1, hb1, hc1]
    <;> ring

  have h6 : a * b * c / (a * b + b * c + c * a) = 1 / (1 / a + 1 / b + 1 / c) := by 
    rw [h5]
    field_simp [ha1, hb1, hc1]

  rw [h6]
  rw [h4]
  all_goals norm_num