import Mathlib

theorem algebra_264955 {x y z w : ℝ} (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (hw : w ≥ 0)
    (h1 : x + y + Real.sqrt z = 4) (h2 : Real.sqrt x * Real.sqrt y - Real.sqrt w = 2) :
    x = 2 ∧ y = 2 ∧ z = 0 ∧ w = 0 := by

  have h3 : Real.sqrt x ^ 2 = x := by 
    rw [Real.sq_sqrt]
    linarith
  have h4 : Real.sqrt y ^ 2 = y := by 
    rw [Real.sq_sqrt]
    linarith
  have h5 : Real.sqrt z ≥ 0 := by 
    apply Real.sqrt_nonneg
  have h6 : Real.sqrt w ≥ 0 := by 
    apply Real.sqrt_nonneg

  have eq2 : Real.sqrt x * Real.sqrt y = 2 + Real.sqrt w := by 
    linarith [h2]

  have h8 : (Real.sqrt x - Real.sqrt y) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (Real.sqrt z), sq_nonneg (Real.sqrt w), 
          Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg z, Real.sqrt_nonneg w, 
          mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y), 
          mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ z by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ w by linarith)]
  have h9 : Real.sqrt x = Real.sqrt y := by 
    nlinarith [h8]

  have h10 : x = y := by 
    have h11 : (Real.sqrt x) ^ 2 = x := by 
      rw [Real.sq_sqrt] 
      linarith
    have h12 : (Real.sqrt y) ^ 2 = y := by 
      rw [Real.sq_sqrt] 
      linarith
    have h13 : Real.sqrt x = Real.sqrt y := h9
    have h14 : (Real.sqrt x) ^ 2 = (Real.sqrt y) ^ 2 := by
      rw [h13]
    nlinarith [h11, h12, h14]

  have h11 : Real.sqrt z = 0 := by 
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z), sq_nonneg (w), 
          Real.sqrt_nonneg z, Real.sqrt_nonneg w, 
          mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ z by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ w by linarith), 
          h10, 
          mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y by linarith)]

  have h13 : z = 0 := by 
    have h14 : Real.sqrt z = 0 := h11 
    have h15 : Real.sqrt z ^ 2 = z := by 
      rw [Real.sq_sqrt] 
      linarith 
    rw [h14] at h15 
    nlinarith

  have h14 : Real.sqrt w = 0 := by
    nlinarith [Real.sqrt_nonneg w, Real.sqrt_nonneg x, Real.sqrt_nonneg y, 
          Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ w by linarith), 
          h10, 
          mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
        ]

  have h15 : w = 0 := by 
    have h16 : Real.sqrt w = 0 := h14 
    have h17 : Real.sqrt w ^ 2 = w := by 
      rw [Real.sq_sqrt] 
      linarith 
    rw [h16] at h17 
    nlinarith

  have h16 : x = 2 := by 
    nlinarith [h1, h10, Real.sqrt_nonneg z, Real.sqrt_nonneg w, h13, h15, Real.sq_sqrt (show (0 : ℝ) ≤ z by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ w by linarith)]

  have h17 : y = 2 := by 
    nlinarith [h10, h16]

  exact ⟨h16, h17, h13, h15⟩