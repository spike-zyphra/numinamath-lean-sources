import Mathlib

theorem number_theory_313559 (a b c : ℤ) (h : a > 0) (h' : b > 0) (h'' : c > 0)
    (h''' : a * b * c + b * c + c * a + a * b + a + b + c = 7) :
    (1 / 2) * a * b * Real.sin (Real.pi / 3) = Real.sqrt 3 / 4 := by
  have h1 : (a + 1) * (b + 1) * (c + 1) = 8 := by 
    nlinarith 
  have h2 : a + 1 ≥ 2 := by 
    omega 
  have h3 : b + 1 ≥ 2 := by 
    omega 
  have h4 : c + 1 ≥ 2 := by 
    omega 
  have h5' : (a + 1) = 2 := by 
    by_cases h12 : a + 1 > 2 
    · -- Assume a + 1 > 2, so a + 1 ≥ 3
      have h13 : a + 1 ≥ 3 := by omega 
      have h6 : (a + 1) * (b + 1) * (c + 1) = 8 := h1 
      have h14 : (b + 1) * (c + 1) ≤ 2 := by 
        nlinarith 
      have h17 : (b + 1) * (c + 1) ≥ 4 := by 
        nlinarith 
      nlinarith 
    · -- Assume not a + 1 > 2, so a + 1 ≤ 2 
      have h14 : a + 1 ≤ 2 := by omega 
      have h15 : a + 1 ≥ 2 := h2 
      have h16 : a + 1 = 2 := by omega 
      linarith 
  have h5 : a = 1 := by 
    linarith [h5']
  have h15 : b + 1 = 2 := by 
    have h16 : (b + 1) * (c + 1) = 4 := by 
      rw [show a + 1 = 2 by linarith [h5']] at h1 
      nlinarith 
    have h17 : b + 1 ≥ 2 := h3 
    have h18 : c + 1 ≥ 2 := h4 
    by_cases h18 : b + 1 > 2 
    · -- Assume b + 1 > 2, so b + 1 ≥ 3 
      have h19 : b + 1 ≥ 3 := by omega 
      nlinarith 
    · -- Assume not b + 1 > 2, so b + 1 ≤ 2 
      have h20 : b + 1 ≤ 2 := by omega 
      have h21 : b + 1 ≥ 2 := h3 
      have h22 : b + 1 = 2 := by omega 
      linarith 
  have h6 : b = 1 := by 
    linarith [h15] 
  -- Now we compute c
  have h16 : c + 1 = 2 := by 
    have h17 : (b + 1) * (c + 1) = 4 := by 
      rw [show a + 1 = 2 by linarith [h5']] at h1 
      nlinarith 
    have h18 : c + 1 ≥ 2 := h4 
    have h22 : b + 1 = 2 := h15 
    rw [show b + 1 = 2 by linarith [h15]] at h17 
    nlinarith 
  have h7 : c = 1 := by 
    linarith [h16] 
  -- Now we compute the area, given a=1, b=1, and angle = 60 degrees (pi/3)
  rw [h5, h6] 
  have h11 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := by 
    rw [Real.sin_pi_div_three]
  rw [h11] 
  all_goals 
    ring_nf