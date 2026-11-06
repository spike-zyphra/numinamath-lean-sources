import Mathlib
open Real

theorem algebra_7294 {a b : ℝ} (ha : a ≠ b)
    (h1 : a ^ 4 + 8 * b = 4 * (a ^ 3 - 1) - 16 * sqrt 3)
    (h2 : b ^ 4 + 8 * a = 4 * (b ^ 3 - 1) + 16 * sqrt 3) :
    a ^ 4 + b ^ 4 = 56 := by

  have h3 : a ^ 4 + b ^ 4 + 8 * (a + b) = 4 * (a ^ 3 + b ^ 3 - 2) := by 
    nlinarith [h1, h2, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  
  have h4 : a ^ 4 + b ^ 4 - 4 * (a ^ 3 + b ^ 3) + 8 * (a + b) + 8 = 0 := by
    nlinarith [h3]
  
  have h5 : (a ^ 2 - 2 * a - 2) ^ 2 + (b ^ 2 - 2 * b - 2) ^ 2 = 0 := by
    nlinarith [h4]

  have ha2 : (a ^ 2 - 2 * a - 2) ^ 2 = 0 := by
    linarith [show (a ^ 2 - 2 * a - 2) ^ 2 ≥ 0 by nlinarith, show (b ^ 2 - 2 * b - 2) ^ 2 ≥ 0 by nlinarith]

  have hb2 : (b ^ 2 - 2 * b - 2) ^ 2 = 0 := by
    linarith [show (a ^ 2 - 2 * a - 2) ^ 2 ≥ 0 by nlinarith, show (b ^ 2 - 2 * b - 2) ^ 2 ≥ 0 by nlinarith]

  have ha1 : a ^ 2 - 2 * a - 2 = 0 := by 
    rwa [sq_eq_zero_iff] at ha2

  have hb1 : b ^ 2 - 2 * b - 2 = 0 := by 
    rwa [sq_eq_zero_iff] at hb2
  
  have ha2' : a ^ 2 = 2 * a + 2 := by linarith

  have hb2' : b ^ 2 = 2 * b + 2 := by linarith
  
  have ha3 : a ^ 3 = 6 * a + 4 := by
    calc 
      a ^ 3 = a * a ^ 2 := by ring
      _ = a * (2 * a + 2) := by rw [ha2']
      _ = 2 * a ^ 2 + 2 * a := by ring
      _ = 2 * (2 * a + 2) + 2 * a := by rw [ha2']
      _ = 6 * a + 4 := by ring
  
  have hb3 : b ^ 3 = 6 * b + 4 := by
    calc 
      b ^ 3 = b * b ^ 2 := by ring
      _ = b * (2 * b + 2) := by rw [hb2']
      _ = 2 * b ^ 2 + 2 * b := by ring
      _ = 2 * (2 * b + 2) + 2 * b := by rw [hb2']
      _ = 6 * b + 4 := by ring
  
  have ha4 : a ^ 4 = 16 * a + 12 := by
    calc 
      a ^ 4 = a * a ^ 3 := by ring
      _ = a * (6 * a + 4) := by rw [ha3]
      _ = 6 * a ^ 2 + 4 * a := by ring
      _ = 6 * (2 * a + 2) + 4 * a := by rw [ha2']
      _ = 16 * a + 12 := by ring
  
  have hb4 : b ^ 4 = 16 * b + 12 := by
    calc 
      b ^ 4 = b * b ^ 3 := by ring
      _ = b * (6 * b + 4) := by rw [hb3]
      _ = 6 * b ^ 2 + 4 * b := by ring
      _ = 6 * (2 * b + 2) + 4 * b := by rw [hb2']
      _ = 16 * b + 12 := by ring
  
  have hab : a + b = 2 := by 
    have h : a ^ 2 - b ^ 2 = 2 * (a - b) := by linarith [ha1, hb1]
    have h' : (a - b) * (a + b) = 2 * (a - b) := by
      have : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
      linarith [this, h]
    
    have hne : a - b ≠ 0 := by
      intro h'
      apply ha
      linarith

    have : a + b = 2 := by 
      apply (mul_right_inj' hne).mp 
      linarith

    linarith
  
  linarith [ha4, hb4, hab]