import Mathlib

theorem algebra_302874 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : Real.sqrt a * (Real.sqrt a + Real.sqrt b) = 3 * Real.sqrt b * (Real.sqrt a + 5 * Real.sqrt b)) :
    (2 * a + 3 * b + Real.sqrt (a * b)) / (a - b + Real.sqrt (a * b)) = 2 := by 
  have ha' : 0 < Real.sqrt a := by
    apply Real.sqrt_pos.mpr
    exact ha
  have hb' : 0 < Real.sqrt b := by
    apply Real.sqrt_pos.mpr
    exact hb
  have h3 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (show 0 ≤ a by linarith)
  have h4 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (show 0 ≤ b by linarith)
  have h5 : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := by
    rw [← Real.sqrt_mul (by linarith)]
    all_goals ring_nf <;> simp [Real.sqrt_mul_self]
  have h6 : Real.sqrt a * (Real.sqrt a + Real.sqrt b) = a + Real.sqrt (a * b) := by
    calc
      Real.sqrt a * (Real.sqrt a + Real.sqrt b)
          = Real.sqrt a ^ 2 + Real.sqrt a * Real.sqrt b := by ring
      _ = a + Real.sqrt a * Real.sqrt b := by rw [h3]
      _ = a + Real.sqrt (a * b) := by rw [h5]
  have h7 : 3 * Real.sqrt b * (Real.sqrt a + 5 * Real.sqrt b) = 3 * Real.sqrt (a * b) + 15 * b := by
    calc
      3 * Real.sqrt b * (Real.sqrt a + 5 * Real.sqrt b)
          = 3 * (Real.sqrt b * Real.sqrt a) + 3 * (5 * Real.sqrt b ^ 2) := by ring
      _ = 3 * (Real.sqrt a * Real.sqrt b) + 3 * (5 * Real.sqrt b ^ 2) := by 
        ring_nf
      _ = 3 * Real.sqrt (a * b) + 3 * (5 * b) := by
        rw [show Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) by linarith [h5]]
        <;> rw [h4]
      _ = 3 * Real.sqrt (a * b) + 15 * b := by ring
  have h8 : a + Real.sqrt (a * b) = 3 * Real.sqrt (a * b) + 15 * b := by
    nlinarith [h, h6, h7]
  have h9 : a = 2 * Real.sqrt (a * b) + 15 * b := by
    nlinarith [h8]
  have h10 : a - 15 * b = 2 * Real.sqrt (a * b) := by 
    linarith [h9]
  have h11 : (a - 15 * b) ^ 2 = 4 * (Real.sqrt (a * b)) ^ 2 := by 
    calc
      (a - 15 * b) ^ 2 = (2 * Real.sqrt (a * b)) ^ 2 := by 
        rw [show a - 15 * b = 2 * Real.sqrt (a * b) by linarith [h10]]
      _ = 4 * (Real.sqrt (a * b) ^ 2) := by 
        ring_nf 
        <;> nlinarith 
  have h12 : (Real.sqrt (a * b)) ^ 2 = a * b := by
    rw [Real.sq_sqrt]
    nlinarith [show 0 ≤ a by linarith, show 0 ≤ b by linarith, mul_pos ha hb]
  have h13 : (a - 15 * b) ^ 2 = 4 * a * b := by
    nlinarith [h11, h12]
  have h14 : (a - 25 * b) * (a - 9 * b) = 0 := by
    nlinarith 
  cases' (mul_eq_zero.mp h14) with h15 h16
  · -- a = 25 * b
    have h17 : a = 25 * b := by linarith [h15]
    have h18 : Real.sqrt (a * b) = 5 * b := by
      rw [show a * b = (5 * b) ^ 2 by
        rw [h17]
        nlinarith [show 0 < b by linarith]
      ]
      <;> field_simp [Real.sqrt_sq_eq_abs, abs_of_pos, mul_pos, h17, hb]
      <;> nlinarith
    have h19 : 2 * a + 3 * b + Real.sqrt (a * b) = 58 * b := by
      rw [h18]
      nlinarith [h17]
    have h20 : a - b + Real.sqrt (a * b) = 29 * b := by
      rw [h18]
      nlinarith [h17]
    have h21 : (2 * a + 3 * b + Real.sqrt (a * b)) / (a - b + Real.sqrt (a * b)) = 2 := by
      rw [h19, h20]
      have hb1 : 0 < (b : ℝ) := hb
      field_simp [hb1]
      <;> nlinarith
      all_goals linarith
    exact h21
  · -- a = 9 * b
    have h22 : a = 9 * b := by linarith [h16]
    have h24 : Real.sqrt (a * b) = 3 * b := by
      rw [show a * b = (3 * b) ^ 2 by
        rw [h22]
        nlinarith [show 0 < b by linarith]
      ]
      <;> field_simp [Real.sqrt_sq_eq_abs, abs_of_pos, mul_pos, h22, hb]
      <;> nlinarith
    nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg a, Real.sqrt_nonneg b, h3, h4, h8, h12, h22, Real.sqrt_nonneg (a * b)]
  all_goals linarith