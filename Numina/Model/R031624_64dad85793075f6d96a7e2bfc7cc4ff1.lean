import Mathlib

theorem inequalities_303212 (x : ℝ) (hx : x ≥ 0) :
    Real.sqrt (x + 3) - Real.sqrt (x + 2) < Real.sqrt (x + 1) - Real.sqrt x := by
  have h1 : Real.sqrt (x + 3) + Real.sqrt x < Real.sqrt (x + 1) + Real.sqrt (x + 2) := by
    have h2 : 0 ≤ Real.sqrt (x + 3) := by positivity
    have h3 : 0 ≤ Real.sqrt x := by positivity
    have h4 : 0 ≤ Real.sqrt (x + 1) := by positivity
    have h5 : 0 ≤ Real.sqrt (x + 2) := by positivity
    have h6 : (Real.sqrt (x + 3) + Real.sqrt x) ^ 2 < (Real.sqrt (x + 1) + Real.sqrt (x + 2)) ^ 2 := by
      have h7 : (Real.sqrt (x + 3) + Real.sqrt x) ^ 2 = (Real.sqrt (x + 3)) ^ 2 + (Real.sqrt x) ^ 2 + 2 * (Real.sqrt (x + 3) * Real.sqrt x) := by
        ring
      have h8 : (Real.sqrt (x + 1) + Real.sqrt (x + 2)) ^ 2 = (Real.sqrt (x + 1)) ^ 2 + (Real.sqrt (x + 2)) ^ 2 + 2 * (Real.sqrt (x + 1) * Real.sqrt (x + 2)) := by
        ring
      rw [h7, h8]
      have h9 : (Real.sqrt (x + 3)) ^ 2 = x + 3 := by
        rw [Real.sq_sqrt]
        linarith
      have h10 : (Real.sqrt x) ^ 2 = x := by
        rw [Real.sq_sqrt]
        linarith
      have h11 : (Real.sqrt (x + 1)) ^ 2 = x + 1 := by
        rw [Real.sq_sqrt]
        linarith
      have h12 : (Real.sqrt (x + 2)) ^ 2 = x + 2 := by
        rw [Real.sq_sqrt]
        linarith
      rw [h9, h10, h11, h12]
      have h15 : Real.sqrt (x + 1) * Real.sqrt (x + 2) > Real.sqrt (x + 3) * Real.sqrt x := by
        have h16 : (Real.sqrt (x + 1) * Real.sqrt (x + 2)) ^ 2 > (Real.sqrt (x + 3) * Real.sqrt x) ^ 2 := by
          have h17 : (Real.sqrt (x + 1) * Real.sqrt (x + 2)) ^ 2 = (x + 1) * (x + 2) := by
            calc
              (Real.sqrt (x + 1) * Real.sqrt (x + 2)) ^ 2
                = (Real.sqrt (x + 1)) ^ 2 * (Real.sqrt (x + 2)) ^ 2 := by ring
              _ = (x + 1) * (x + 2) := by
                rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
          have h18 : (Real.sqrt (x + 3) * Real.sqrt x) ^ 2 = (x + 3) * x := by
            calc
              (Real.sqrt (x + 3) * Real.sqrt x) ^ 2
                = (Real.sqrt (x + 3)) ^ 2 * (Real.sqrt x) ^ 2 := by ring
              _ = (x + 3) * x := by
                rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
          rw [h17, h18]
          nlinarith
        have h17 : 0 ≤ Real.sqrt (x + 1) * Real.sqrt (x + 2) := by positivity
        have h18 : 0 ≤ Real.sqrt (x + 3) * Real.sqrt x := by positivity
        nlinarith [Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (x + 2), Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg x]
      nlinarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg x, Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (x + 2),
        h15]
    have h30 : 0 ≤ Real.sqrt (x + 3) + Real.sqrt x := by positivity
    have h31 : 0 ≤ Real.sqrt (x + 1) + Real.sqrt (x + 2) := by positivity
    nlinarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg x, Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (x + 2),
      h6, mul_nonneg (Real.sqrt_nonneg (x + 3)) (Real.sqrt_nonneg x), mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (x + 2)), h30, h31
    ]
  nlinarith [h1, Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x + 2), Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg x]