import Mathlib

theorem algebra_107462 {a : ℝ} (ha : a^3 - a - 1 = 0) :
    (a + Real.sqrt 2)^6 - 8 * (a + Real.sqrt 2)^4 - 2 * (a + Real.sqrt 2)^3 +
    13 * (a + Real.sqrt 2)^2 - 10 * (a + Real.sqrt 2) - 1 = 0 := by
  have h1 : a ^ 3 = a + 1 := by linarith
  have h2 : a ^ 4 = a ^ 2 + a := by 
    calc
      a ^ 4 = a * a ^ 3 := by ring 
      _ = a * (a + 1) := by rw [h1]
      _ = a ^ 2 + a := by ring 
  have h3 : a ^ 5 = a ^ 2 + a + 1 := by 
    calc 
      a ^ 5 = a * a ^ 4 := by ring 
      _ = a * (a ^ 2 + a) := by rw [h2]
      _ = a ^ 3 + a ^ 2 := by ring 
      _ = (a + 1) + a ^ 2 := by rw [h1]
      _ = a ^ 2 + a + 1 := by ring 
  have h4 : a ^ 6 = a ^ 2 + 2 * a + 1 := by 
    calc 
      a ^ 6 = (a ^ 3) ^ 2 := by ring 
      _ = (a + 1) ^ 2 := by rw [h1]
      _ = a ^ 2 + 2 * a + 1 := by ring 
  have h5 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h6 : Real.sqrt 2 ^ 4 = (2 : ℝ) ^ 2 := by 
    calc 
      Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring 
      _ = (2 : ℝ) ^ 2 := by rw [h5]
  have h7 : Real.sqrt 2 ^ 6 = (2 : ℝ) ^ 3 := by 
    calc 
      Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := by ring 
      _ = (2 : ℝ) ^ 3 := by rw [h5]

  have h8 : (a + Real.sqrt 2) ^ 2 = a ^ 2 + 2 * a * Real.sqrt 2 + 2 := by 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]

  have h9 : (a + Real.sqrt 2) ^ 3 = a ^ 3 + 3 * a ^ 2 * Real.sqrt 2 + 3 * a * 2 + 2 * Real.sqrt 2 := by 
    calc 
      (a + Real.sqrt 2) ^ 3 = (a + Real.sqrt 2) * (a + Real.sqrt 2) ^ 2 := by ring 
      _ = (a + Real.sqrt 2) * (a ^ 2 + 2 * a * Real.sqrt 2 + 2) := by rw [h8]
      _ = a * (a ^ 2 + 2 * a * Real.sqrt 2 + 2) + Real.sqrt 2 * (a ^ 2 + 2 * a * Real.sqrt 2 + 2) := by ring 
      _ = (a ^ 3 + 2 * a ^ 2 * Real.sqrt 2 + 2 * a) + (a ^ 2 * Real.sqrt 2 + 2 * a * (Real.sqrt 2 ^ 2) + 2 * Real.sqrt 2) := by ring 
      _ = a ^ 3 + 3 * a ^ 2 * Real.sqrt 2 + 3 * a * 2 + 2 * Real.sqrt 2 := by 
        have h5' : Real.sqrt 2 ^ 2 = 2 := h5 
        rw [h5'] 
        all_goals ring_nf <;> nlinarith 
        all_goals nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        all_goals ring 

  have h10 : (a + Real.sqrt 2) ^ 4 = (a + Real.sqrt 2) ^ 2 * (a + Real.sqrt 2) ^ 2 := by 
    ring
  have h11 : (a + Real.sqrt 2) ^ 4 = (a ^ 2 + 2 * a * Real.sqrt 2 + 2) ^ 2 := by 
    rw [h10, h8]
    all_goals ring_nf 

  have h12 : (a + Real.sqrt 2) ^ 6 = (a + Real.sqrt 2) ^ 2 * (a + Real.sqrt 2) ^ 2 * (a + Real.sqrt 2) ^ 2 := by 
    ring
  have h13 : (a + Real.sqrt 2) ^ 6 = (a ^ 2 + 2 * a * Real.sqrt 2 + 2) ^ 3 := by 
    rw [h12, h8]
    all_goals ring_nf <;> nlinarith 
    all_goals nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

  rw [show (a + Real.sqrt 2) ^ 6 = (a ^ 2 + 2 * a * Real.sqrt 2 + 2) ^ 3 by linarith [h13]]
  rw [show (a + Real.sqrt 2) ^ 4 = (a ^ 2 + 2 * a * Real.sqrt 2 + 2) ^ 2 by linarith [h11]]
  rw [show (a + Real.sqrt 2) ^ 3 = a ^ 3 + 3 * a ^ 2 * Real.sqrt 2 + 3 * a * 2 + 2 * Real.sqrt 2 by linarith [h9]]
  rw [show (a + Real.sqrt 2) ^ 2 = a ^ 2 + 2 * a * Real.sqrt 2 + 2 by linarith [h8]]

  ring_nf
  <;> simp only [pow_succ, h1, h2, h3, h4, Real.sqrt_sq, h5, h6, h7] at *
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), sq_nonneg (a), sq_nonneg (Real.sqrt 2), sq_nonneg (a * Real.sqrt 2)]