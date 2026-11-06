import Mathlib

theorem algebra_289657 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h1 : Real.sqrt (Real.sqrt x + 2) = y - 2) (h2 : Real.sqrt (Real.sqrt y + 2) = x - 2) :
    x = 4 ∧ y = 4 := by

  have h1' : Real.sqrt x + 2 = (y - 2) ^ 2 := by 
    calc 
      Real.sqrt x + 2 = (Real.sqrt (Real.sqrt x + 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        nlinarith [Real.sqrt_nonneg x]
      _ = (y - 2) ^ 2 := by 
        rw [h1]

  have h2' : Real.sqrt y + 2 = (x - 2) ^ 2 := by
    calc 
      Real.sqrt y + 2 = (Real.sqrt (Real.sqrt y + 2)) ^ 2 := by
        rw [Real.sq_sqrt]
        nlinarith [Real.sqrt_nonneg y]
      _ = (x - 2) ^ 2 := by 
        rw [h2]

  have hx2 : x ≥ 2 := by
    by_contra h
    push_neg at h
    have h4 : x - 2 < 0 := by linarith 
    have h5 : Real.sqrt (Real.sqrt y + 2) ≥ 0 := Real.sqrt_nonneg (Real.sqrt y + 2)
    nlinarith

  have hy2 : y ≥ 2 := by
    by_contra h 
    push_neg at h 
    have h6 : y - 2 < 0 := by linarith
    have h7 : Real.sqrt (Real.sqrt x + 2) ≥ 0 := Real.sqrt_nonneg (Real.sqrt x + 2)
    nlinarith

  have h3x : x = 4 := by 
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 4), 
      Real.sqrt_nonneg x, Real.sqrt_nonneg y, 
      sq_nonneg (Real.sqrt x - 2), sq_nonneg (Real.sqrt y - 2), 
      Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ y by linarith), 
      mul_nonneg (show 0 ≤ Real.sqrt x by apply Real.sqrt_nonneg) (show 0 ≤ Real.sqrt y by apply Real.sqrt_nonneg)
    ]
  have h3y : y = 4 := by 
    nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 4), 
      Real.sqrt_nonneg x, Real.sqrt_nonneg y, 
      sq_nonneg (Real.sqrt x - 2), sq_nonneg (Real.sqrt y - 2), 
      Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ y by linarith), 
      mul_nonneg (show 0 ≤ Real.sqrt x by apply Real.sqrt_nonneg) (show 0 ≤ Real.sqrt y by apply Real.sqrt_nonneg)
    ]
  exact ⟨h3x, h3y⟩