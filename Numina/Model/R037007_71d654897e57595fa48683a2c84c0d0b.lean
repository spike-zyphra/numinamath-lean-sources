import Mathlib

theorem algebra_172666 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h1 : a > b)
    (h2 : a * Real.sqrt a + b * Real.sqrt b = 134) (h3 : a * Real.sqrt b + b * Real.sqrt a = 126) :
    a = 81 / 4 ∧ b = 49 / 4 := by

  have ha2 : 0 < Real.sqrt a := by
    apply Real.sqrt_pos.mpr
    linarith
  have hb2 : 0 < Real.sqrt b := by
    apply Real.sqrt_pos.mpr
    linarith
  have h4 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
  have h5 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)

  have eq1 : a * Real.sqrt a = (Real.sqrt a) ^ 3 := by
    calc
      a * Real.sqrt a = (Real.sqrt a) ^ 2 * Real.sqrt a := by 
        have h6 : (Real.sqrt a) ^ 2 = a := by
          linarith [Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith)]
        rw [h6]
      _ = (Real.sqrt a) ^ 3 := by ring

  have eq2 : b * Real.sqrt b = (Real.sqrt b) ^ 3 := by
    calc
      b * Real.sqrt b = (Real.sqrt b) ^ 2 * Real.sqrt b := by 
        have h7 : (Real.sqrt b) ^ 2 = b := by 
          linarith [Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith)]
        rw [h7]
      _ = (Real.sqrt b) ^ 3 := by ring

  have h6 : (Real.sqrt a) ^ 3 + (Real.sqrt b) ^ 3 = 134 := by 
    linarith [h2, eq1, eq2]

  have eq3 : a * Real.sqrt b = (Real.sqrt a) ^ 2 * (Real.sqrt b) := by
    calc
      a * Real.sqrt b = (Real.sqrt a) ^ 2 * (Real.sqrt b) := by
        have h8 : (Real.sqrt a) ^ 2 = a := by 
          linarith [Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith)]
        rw [h8]
      _ = (Real.sqrt a) ^ 2 * (Real.sqrt b) := by ring

  have eq4 : b * Real.sqrt a = (Real.sqrt b) ^ 2 * (Real.sqrt a) := by
    calc
      b * Real.sqrt a = (Real.sqrt b) ^ 2 * (Real.sqrt a) := by 
        have h9 : (Real.sqrt b) ^ 2 = b := by 
          linarith [Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith)]
        rw [h9]
      _ = (Real.sqrt b) ^ 2 * (Real.sqrt a) := by ring

  have h7 : (Real.sqrt a) ^ 2 * (Real.sqrt b) + (Real.sqrt b) ^ 2 * (Real.sqrt a) = 126 := by 
    linarith [h3, eq3, eq4]

  have hS : (Real.sqrt a + Real.sqrt b) ^ 3 = 512 := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a * Real.sqrt b), h6, h7, mul_pos ha hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b, sq_pos_of_pos (show Real.sqrt a > 0 by positivity)]

  have h8 : Real.sqrt a + Real.sqrt b = 8 := by
    have h9 : (Real.sqrt a + Real.sqrt b) ^ 3 = 512 := hS
    have h10 : Real.sqrt a + Real.sqrt b > 0 := by
      have h11 : Real.sqrt a > 0 := by
        apply Real.sqrt_pos.2
        linarith
      have h12 : Real.sqrt b > 0 := by
        apply Real.sqrt_pos.2
        linarith
      linarith
    have h11 : Real.sqrt a + Real.sqrt b = 8 := by
      have h12 : (Real.sqrt a + Real.sqrt b) ^ 3 = 512 := h9
      have h13 : Real.sqrt a + Real.sqrt b > 0 := h10
      have h14 : Real.sqrt a + Real.sqrt b = 8 := by
        have h17 : (Real.sqrt a + Real.sqrt b)  ^ 3 - 512 = 0 := by linarith
        have h18 : (Real.sqrt a + Real.sqrt b - 8) * ((Real.sqrt a + Real.sqrt b) ^ 2 + 8 * (Real.sqrt a + Real.sqrt b) + 64) = 0 := by
          nlinarith [sq_nonneg ((Real.sqrt a + Real.sqrt b) - 8)]
        cases' (mul_eq_zero.mp h18) with h19 h20
        · linarith
        · 
          nlinarith [sq_nonneg ((Real.sqrt a + Real.sqrt b) + 4)]
      exact h14
    exact h11

  have hP : Real.sqrt a * Real.sqrt b = 63 / 4 := by
    have h11 : (Real.sqrt a)  ^ 2 * (Real.sqrt b) + (Real.sqrt b)  ^ 2 * (Real.sqrt a) = 126 := h7
    have h12 : Real.sqrt a + Real.sqrt b = 8 := h8
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a * Real.sqrt b), mul_pos ha hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

  have h12 : Real.sqrt a = 9 / 2 := by
    have h11 : Real.sqrt a + Real.sqrt b = 8 := h8
    have h12 : Real.sqrt a * Real.sqrt b = 63 / 4 := hP
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a - 9 / 2), sq_nonneg (Real.sqrt b - 7 / 2), Real.sqrt_nonneg a, Real.sqrt_nonneg b, h1]

  have h13 : Real.sqrt b = 7 / 2 := by
    nlinarith [h8, h12, Real.sqrt_nonneg a, Real.sqrt_nonneg b, h1]

  have ha1 : a = 81 / 4 := by
    calc
      a = (Real.sqrt a)  ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = (9 / 2)  ^ 2 := by 
        rw [h12]
      _ = (81 / 4) := by
        norm_num

  have hb1 : b = 49 / 4 := by
    calc
      b = (Real.sqrt b)  ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = (7 / 2)  ^ 2 := by 
        rw [h13]
      _ = (49 / 4) := by 
        norm_num

  exact ⟨ha1, hb1⟩