import Mathlib

theorem inequalities_321959 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (x y : ℝ) (hx : x = (b^2 + 1) / a) (hy : y = (a^2 + 1) / b) :
    max x y > 2 := by 
  by_contra h
  have h1 : x ≤ 2 := by
    have h2 : max x y ≤ (2 : ℝ) := by linarith [h]
    have h3 : x ≤ max x y := by apply le_max_left
    linarith
  have h2 : y ≤ 2 := by
    have h4 : max x y ≤ (2 : ℝ) := by linarith [h]
    have h5 : y ≤ max x y := by apply le_max_right
    linarith
  have h3 : x = (b ^ 2 + 1) / a := by linarith [hx]
  have h4 : y = (a ^ 2 + 1) / b := by linarith [hy]
  have h5 : (b ^ 2 + 1) / a ≤ 2 := by
    linarith [h1, h3]
  have h6 : (a ^ 2 + 1) / b ≤ 2 := by
    linarith [h2, h4]
  have h7 : b ^ 2 + 1 ≤ 2 * a := by 
    have h3' : (b ^ 2 + 1) / a ≤ (2 : ℝ) := by 
      linarith [h5]
    have h6' : 0 < a := by linarith
    have h7' : b ^ 2 + 1 ≤ (2 * a) := by 
      have h8' : (b ^ 2 + 1) / a ≤ (2 : ℝ) := by 
        linarith [h3']
      have pos1 : 0 < a := by linarith
      have : b ^ 2 + 1 ≤ (2 * a) := by
        have h4' : (b ^ 2 + 1) / a ≤ (2 : ℝ) := by linarith [h8']
        have : b ^ 2 + 1 ≤ (2 * a) := by
          apply (div_le_iff₀ pos1).mp at h4'
          linarith
        linarith
      linarith
    linarith
  have h8 : a ^ 2 + 1 ≤ 2 * b := by 
    have h4' : (a ^ 2 + 1) / b ≤ (2 : ℝ) := by 
      linarith [h6]
    have h3' : 0 < b := by linarith
    have h7' : a ^ 2 + 1 ≤ (2 * b) := by 
      have h8' : (a ^ 2 + 1) / b ≤ (2 : ℝ) := by 
        linarith [h4']
      have pos1 : 0 < b := by linarith
      have : a ^ 2 + 1 ≤ (2 * b) := by 
        have h4' : (a ^ 2 + 1) / b ≤ (2 : ℝ) := by linarith [h8']
        have : a ^ 2 + 1 ≤ (2 * b) := by 
          apply (div_le_iff₀ pos1).mp at h4'
          linarith
        linarith
      linarith
    linarith
  have h11 : (a - 1) ^ 2 + (b - 1) ^ 2 ≤ 0 := by
    nlinarith 
  have h12 : (a - 1) ^ 2 ≥ 0 := by
    nlinarith 
  have h13 : (b - 1) ^ 2 ≥ 0 := by
    nlinarith 
  have h14 : (a - 1) ^ 2 = 0 := by
    nlinarith 
  have h15 : (b - 1) ^ 2 = 0 := by
    nlinarith 
  have h16 : a - 1 = 0 := by
    nlinarith 
  have h17 : b - 1 = 0 := by
    nlinarith 
  have h18 : a = 1 := by linarith 
  have h19 : b = 1 := by linarith 
  have h20 : a = b := by
    linarith [h18, h19]
  tauto