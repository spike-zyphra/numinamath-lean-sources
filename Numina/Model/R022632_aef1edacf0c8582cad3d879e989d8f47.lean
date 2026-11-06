import Mathlib

theorem algebra_173098 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a > b)
    (h1 : a * Real.sqrt a + b * Real.sqrt b = 134) (h2 : a * Real.sqrt b + b * Real.sqrt a = 126) :
    (a, b) = (81 / 4, 49 / 4) := by

  have ha2 : 0 ≤ a := by linarith
  have hb2 : 0 ≤ b := by linarith
  have h3 : Real.sqrt a ^ 2 = a := by
    rw [Real.sq_sqrt]
    linarith
  have h4 : Real.sqrt b ^ 2 = b := by
    rw [Real.sq_sqrt]
    linarith

  have eq1 : Real.sqrt a ^ 3 + Real.sqrt b ^ 3 = 134 := by
    calc
      Real.sqrt a ^ 3 + Real.sqrt b ^ 3 = (a * Real.sqrt a) + (b * Real.sqrt b) := by
        have h5 : Real.sqrt a ^ 3 = (a) * Real.sqrt a := by
          calc
            Real.sqrt a ^ 3 = (Real.sqrt a) ^ 2 * Real.sqrt a := by ring
            _ = a * Real.sqrt a := by
              rw [h3]
        have h6 : Real.sqrt b ^ 3 = (b) * Real.sqrt b := by
          calc
            Real.sqrt b ^ 3 = (Real.sqrt b) ^ 2 * Real.sqrt b := by ring
            _ = b * Real.sqrt b := by
              rw [h4]
        rw [h5, h6]
      _ = 134 := by
        linarith

  have eq2 : Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b) = 126 := by
    calc
      Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b) = (a * Real.sqrt b) + (b * Real.sqrt a) := by
        have h5 : Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b) =
          ( Real.sqrt a ^ 2 * Real.sqrt b ) + ( Real.sqrt b ^ 2 * Real.sqrt a ) := by
            ring
        rw [h5]
        have h7 : Real.sqrt a ^ 2 = a := by
          rw [Real.sq_sqrt]
          linarith
        have h8 : Real.sqrt b ^ 2 = b := by
          rw [Real.sq_sqrt]
          linarith
        rw [h7, h8]
        <;> nlinarith [show Real.sqrt a > 0 by apply Real.sqrt_pos.mpr; linarith, show Real.sqrt b > 0 by apply Real.sqrt_pos.mpr; linarith]
      _ = 126 := by
        linarith

  have eq3 : Real.sqrt a + Real.sqrt b = 8 := by
    have h5 : (Real.sqrt a + Real.sqrt b) ^ 3 = 512 := by
      nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a + Real.sqrt b - 8), eq1, eq2, mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb) ]
    have h6 : (Real.sqrt a + Real.sqrt b) ^ 3 - 512 = 0 := by
      nlinarith
    have h7 : (Real.sqrt a + Real.sqrt b - 8) * ((Real.sqrt a + Real.sqrt b) ^ 2 + (Real.sqrt a + Real.sqrt b) * 8 + 64) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Real.sqrt a + Real.sqrt b - 8 = 0
      linarith
    · -- (Real.sqrt a + Real.sqrt b) ^ 2 + (Real.sqrt a + Real.sqrt b) * 8 + 64 = 0
      nlinarith [show (Real.sqrt a + Real.sqrt b) ^ 2 ≥ 0 by positivity, show (Real.sqrt a + Real.sqrt b) ≥ 0 by positivity, sq_nonneg ((Real.sqrt a + Real.sqrt b) + 4) ]

  have eq4 : Real.sqrt a * Real.sqrt b = 63 / 4 := by
    nlinarith [eq2, eq3]

  have eq5 : Real.sqrt a > Real.sqrt b := by
    nlinarith [Real.sqrt_nonneg b, Real.sqrt_nonneg a, h, h3, h4 ]

  have h5 : (Real.sqrt a - 9 / 2) * (Real.sqrt b - 7 / 2) = 0 := by
    nlinarith [eq3, eq4, Real.sqrt_nonneg b, Real.sqrt_nonneg a, sq_nonneg (Real.sqrt a - Real.sqrt b) ]

  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Real.sqrt a = 9/2
    have ha8 : Real.sqrt a = 9 / 2 := by
      nlinarith
    have hb8 : Real.sqrt b = 7 / 2 := by
      nlinarith [eq3, ha8 ]
    have ha2' : a = 81 / 4 := by
      calc
        a = (Real.sqrt a) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (9 / 2) ^ 2 := by
          rw [ha8]
        _ = 81 / 4 := by
          norm_num
    have hb2' : b = 49 / 4 := by
      calc
        b = (Real.sqrt b) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (7 / 2) ^ 2 := by
          rw [hb8]
        _ = 49 / 4 := by
          norm_num
    simp [Prod.ext_iff, ha2', hb2']
    all_goals try { nlinarith }
  · -- Real.sqrt b = 7/2
    have hb8 : Real.sqrt b = 7 / 2 := by
      nlinarith
    have ha8 : Real.sqrt a = 9 / 2 := by
      nlinarith [eq3, hb8 ]
    have ha2' : a = 81 / 4 := by
      calc
        a = (Real.sqrt a) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (9 / 2) ^ 2 := by
          rw [ha8]
        _ = 81 / 4 := by
          norm_num
    have hb2' : b = 49 / 4 := by
      calc
        b = (Real.sqrt b) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (7 / 2) ^ 2 := by
          rw [hb8]
        _ = 49 / 4 := by
          norm_num
    simp [Prod.ext_iff, ha2', hb2']
    all_goals try { nlinarith }